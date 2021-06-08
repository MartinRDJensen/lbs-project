module Impl.NeedSchr

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST

module Spec = Spec.NeedSchr

open FStar.HyperStack.ST
open Memcpy

// open Lib.RandomBuffer.System
// open Hacl.NaCl

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

noextract let join4 (l1, l2, l3, l4: (S.seq 'a & S.seq 'a & S.seq 'a & S.seq 'a))
    = S.(l1 @| l2 @| l3 @| l4)

(*
type m3t = ciphertext (key & host)
type m2t =  ciphertext (nonce & key & host & m3t)
*)
noextract let joinCipher (v:Spec.m2t) =
    let _, t = v in
    let n, k, h, m3 = t in
    let _, tt = m3 in
    let inner_key, inner_host = tt in 
    S.(n @| k @| h @|  inner_key @| inner_host)

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

noextract let toSeq (l1: (S.seq 'a))
    = S.(l1)


(*
    let handshake_A (kAS, b, nA: state1_At) (m2: m2t): option (state2_At & m3t) =
    match decrypt kAS m2 with
    | None -> None
    | Some (nA', kAB, b', m3) ->
    if nA' = nA && b' = b
    then Some (kAB, m3)
    else None

#push-options "--z3rlimit 10"
let handshake_A (kAS, b, nA: state1_At) (m2: m2t) (state: state2_At) (m3: m3t) =
(requires fun h -> 
    let open B in
    live h kAS /\ live h b /\ live h nA /\ live h m2 /\
    disjoint state kAS /\ disjoint state b /\ disjoint state nA /\ disjoint state m2 /\
    disjoint m3 kAS /\ disjoint m3 b /\ disjoint m3 nA /\ disjoint m3 m2
)
(ensures fun h0 _ h1 ->
    let open M in
    let state', m3' = Spec.handshake_A (B.as_seq h0 kAS, b, nA) (B.as_seq h0 m2) in
    True
)
= ()
#pop-options
*)

(*
#push-options "--z3rlimit 10"
let generate_key_S (kAS kBS kAB: key) (a b:host) (nA:nonce) (*(m1:m1t)*) (m2: m2t) (e: host): Stack unit
    (requires fun h ->
        let open B in (*Buffer*)
        (*let a, b, nA = m1 in*)
        live h kAS /\ live h kBS /\ live h kAB /\  (*live h m1 /\*) live h m2 /\ live h e /\ live h a /\ live h b /\ live h nA /\
        disjoint m2 kAS /\ disjoint m2 kBS /\ disjoint m2 kAB /\ (*disjoint m2 m1 /\*) disjoint m2 a /\ disjoint m2 b /\ disjoint m2 nA /\
        disjoint e kAS /\ disjoint e kBS /\ disjoint e kAB /\ (*disjoint e m1) *) disjoint e a /\ disjoint e b /\ disjoint e nA)
    (ensures fun h0 _ h1 ->
        let open M in (*Modifies*)
        (*let a, b, nA = m1 in*)
        (*
            let generate_key_S (kAS kBS: key) (a, b, nA: m1t) (kAB: key): m2t & host =
            let m2', e' = Spec.generate_key_S (B.as_seq h0 kAS) (B.as_seq h0 kBS) (B.as_seq h0 a, b, nA) (B.as_seq h0 kAB) in
        *)
        let m2', e' = Spec.generate_key_S (B.as_seq h0 kAS) (B.as_seq h0 kBS)  (B.as_seq h0 a, b, nA) (B.as_seq h0 kAB) in
        (*let state', m1' = Spec.initiate_A (B.as_seq h0 kAS) (B.as_seq h0 a) (B.as_seq h0 b) (B.as_seq h0 nA) in*)
        modifies (loc_union (loc_buffer m2) (loc_buffer e)) h0 h1  (* modifies l (abstract location) h0 (initial heap) h1(resulting heap) *) /\
        B.as_seq h1 e `S.equal` toSeq e' /\
        B.as_seq h1 m2 `S.equal` joinCipher m2' /\
        
        (*
        type m2t = ciphertext (nonce & key & host & m3t)
            
            should encrypt but we cannot use hacl?
        *)
        True
        )
= ()
#pop-options
*)