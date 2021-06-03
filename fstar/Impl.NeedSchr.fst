module Impl.NeedSchr

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST

module Spec = Spec.NeedSchr

open FStar.HyperStack.ST
open LowStar.BufferOps

// open Lib.RandomBuffer.System
// open Hacl.NaCl

// From https://fstarlang.github.io/lowstar/html/ExampleMemCpy.html
let slice_plus_one #a (s1 s2: S.seq a) (i: nat): Lemma
    (requires (
        i < S.length s1 /\
        i < S.length s2 /\
        S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
        S.index s1 i == S.index s2 i))
    (ensures (
        S.equal (S.slice s1 0 (i + 1)) (S.slice s2 0 (i + 1))))
    [ SMTPat (S.slice s1 0 (i + 1)); SMTPat (S.slice s2 0 (i + 1)) ]
=
    let x = S.index s1 i in
    let s1' = S.append (S.slice s1 0 i) (S.cons x S.empty) in
    let s2' = S.append (S.slice s2 0 i) (S.cons x S.empty) in
    assert (S.equal s1' (S.slice s1 0 (i + 1)));
    assert (S.equal s2' (S.slice s2 0 (i + 1)))

val memcpy: #a:eqtype -> src:B.buffer a -> dst:B.buffer a -> len:U32.t -> Stack unit
    (requires fun h0 ->
        let l_src = M.loc_buffer src in
        let l_dst = M.loc_buffer dst in
        B.live h0 src /\ B.live h0 dst /\
        B.length src = U32.v len /\
        B.length dst = U32.v len /\
        M.loc_disjoint l_src l_dst)
    (ensures fun h0 () h1 ->
        let l_src = M.loc_buffer src in
        let l_dst = M.loc_buffer dst in
        B.live h1 src /\
        B.live h1 dst /\
        M.(modifies l_dst h0 h1) /\
        S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
let memcpy #a src dst len =
    let h0 = ST.get () in
    let inv h (i: nat) =
        B.live h src /\ B.live h dst /\
        M.(modifies (loc_buffer dst) h0 h) /\
        i <= U32.v len /\
        S.equal (Seq.slice (B.as_seq h src) 0 i) (Seq.slice (B.as_seq h dst) 0 i)
    in
    let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v len }): Stack unit
        (requires (fun h -> inv h (U32.v i)))
        (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
=
    let open B in
    dst.(i) <- src.(i) in
    C.Loops.for 0ul len inv body

noextract inline_for_extraction let key_length = 32ul
noextract inline_for_extraction let nonce_length = 24ul
noextract inline_for_extraction let host_length = 6ul

noextract inline_for_extraction let state_length = U32.(key_length +^ nonce_length +^ host_length)

noextract inline_for_extraction let cipher_header_length = U32.(16ul +^ nonce_length)

noextract inline_for_extraction let state1_A_length = U32.(key_length +^ host_length +^ nonce_length)
noextract inline_for_extraction let state2_A_length = key_length
noextract inline_for_extraction let state_B_length = U32.(key_length +^ nonce_length)

noextract inline_for_extraction let message1_length = U32.(host_length +^ host_length +^ nonce_length)
noextract inline_for_extraction let message3_length = U32.(cipher_header_length +^ key_length +^ host_length)
noextract inline_for_extraction let message2_length = U32.(cipher_header_length +^ nonce_length +^ key_length +^ host_length +^ message3_length)
noextract inline_for_extraction let message4_length = U32.(cipher_header_length +^ nonce_length)
noextract inline_for_extraction let message5_length = U32.(cipher_header_length +^ nonce_length)

noextract inline_for_extraction type key   = b: B.buffer U8.t{B.length b = U32.v key_length}
noextract inline_for_extraction type host  = b: B.buffer U8.t{B.length b = U32.v host_length}
noextract inline_for_extraction type nonce = b: B.buffer U8.t{B.length b = U32.v nonce_length}

noextract inline_for_extraction type state1_At = b: B.buffer U8.t{B.length b = U32.v state1_A_length}
noextract inline_for_extraction type state2_At = b: B.buffer U8.t{B.length b = U32.v state2_A_length}
noextract inline_for_extraction type state_Bt  = b: B.buffer U8.t{B.length b = U32.v state_B_length}

noextract inline_for_extraction type m1t = b: B.buffer U8.t{B.length b = U32.v message1_length}
noextract inline_for_extraction type m3t = b: B.buffer U8.t{B.length b = U32.v message3_length}
noextract inline_for_extraction type m2t = b: B.buffer U8.t{B.length b = U32.v message2_length}
noextract inline_for_extraction type m4t = b: B.buffer U8.t{B.length b = U32.v message4_length}
noextract inline_for_extraction type m5t = b: B.buffer U8.t{B.length b = U32.v message5_length}

assume val new_key: (r: key) -> EXT unit
assume val new_host: (r: host) -> EXT unit
assume val new_nonce: (r: nonce) -> EXT unit

effect Mem (a: Type) (b: B.buffer U8.t) = Stack a
    (requires fun h -> B.live h b)
    (ensures  fun h0 _ h1 -> ST.modifies_none h0 h1)

noextract let join3 (l1, l2, l3: (S.seq 'a & S.seq 'a & S.seq 'a))
    = S.(l1 @| l2 @| l3)

#push-options "--z3rlimit 10"
let initiate_A (kAS: key) (a b: host) (nA: nonce) (state: state1_At) (m1: m1t): Stack unit
    (requires fun h ->
        let open B in
        live h kAS /\ live h a /\ live h b /\ live h nA /\
        live h state /\ live h m1 /\
        disjoint state kAS /\ disjoint state a /\ disjoint state b /\ disjoint state nA /\
        disjoint m1 kAS /\ disjoint m1 a /\ disjoint m1 b /\ disjoint m1 nA /\
        disjoint state m1)
    (ensures  fun h0 _ h1 ->
        let open M in
        let state', m1' = Spec.initiate_A (B.as_seq h0 kAS) (B.as_seq h0 a) (B.as_seq h0 b) (B.as_seq h0 nA) in
        modifies (loc_union (loc_buffer state) (loc_buffer m1)) h0 h1 /\
        B.as_seq h1 state `S.equal` join3 state' /\
        B.as_seq h1 m1 `S.equal` join3 m1' /\
        True)
=
    let open U32 in
    // state
    memcpy kAS (B.sub state 0ul key_length) key_length;
    memcpy b   (B.sub state key_length host_length) host_length;
    memcpy nA  (B.sub state (key_length +^ host_length) nonce_length) nonce_length;
    // m1
    memcpy a  (B.sub m1 0ul host_length) host_length;
    memcpy b  (B.sub m1 host_length host_length) host_length;
    memcpy nA (B.sub m1 (host_length +^ host_length) nonce_length) nonce_length;
    ()
#pop-options
