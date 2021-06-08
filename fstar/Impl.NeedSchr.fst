module Impl.NeedSchr

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module H = FStar.HyperStack
module ST = FStar.HyperStack.ST

module Spec = Spec.NeedSchr

open FStar.HyperStack.ST
open LowStar.BufferOps
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

noextract inline_for_extraction let m1_length = U32.(host_length +^ host_length +^ nonce_length)
noextract inline_for_extraction let m3_length = U32.(cipher_header_length +^ key_length +^ host_length)
noextract inline_for_extraction let m2_length = U32.(cipher_header_length +^ nonce_length +^ key_length +^ host_length +^ m3_length)
noextract inline_for_extraction let m4_length = U32.(cipher_header_length +^ nonce_length)
noextract inline_for_extraction let m5_length = U32.(cipher_header_length +^ nonce_length)

noextract inline_for_extraction let state1_A_kAS = 0ul
noextract inline_for_extraction let state1_A_b   = U32.(state1_A_kAS +^ key_length)
noextract inline_for_extraction let state1_A_nA  = U32.(state1_A_b   +^ host_length)

noextract inline_for_extraction type key   = b: B.buffer U8.t{B.length b = U32.v key_length}
noextract inline_for_extraction type host  = b: B.buffer U8.t{B.length b = U32.v host_length}
noextract inline_for_extraction type nonce = b: B.buffer U8.t{B.length b = U32.v nonce_length}

noextract inline_for_extraction type state1_At = b: B.buffer U8.t{B.length b = U32.v state1_A_length}
noextract inline_for_extraction type state2_At = b: B.buffer U8.t{B.length b = U32.v state2_A_length}
noextract inline_for_extraction type state_Bt  = b: B.buffer U8.t{B.length b = U32.v state_B_length}

noextract inline_for_extraction type m1t = b: B.buffer U8.t{B.length b = U32.v m1_length}
noextract inline_for_extraction type m2t = b: B.buffer U8.t{B.length b = U32.v m2_length}
noextract inline_for_extraction type m3t = b: B.buffer U8.t{B.length b = U32.v m3_length}
noextract inline_for_extraction type m4t = b: B.buffer U8.t{B.length b = U32.v m4_length}
noextract inline_for_extraction type m5t = b: B.buffer U8.t{B.length b = U32.v m5_length}

noextract inline_for_extraction let m1_a = 0ul
noextract inline_for_extraction let m1_b = U32.(m1_a +^ host_length)
noextract inline_for_extraction let m1_nA = U32.(m1_b +^ host_length)

noextract inline_for_extraction let m2_nA = 0ul
noextract inline_for_extraction let m2_kAB = U32.(m2_nA +^ nonce_length)
noextract inline_for_extraction let m2_b = U32.(m2_kAB +^ key_length)
noextract inline_for_extraction let m2_m3 = U32.(m2_b +^ host_length)

noextract inline_for_extraction let m3_kAB = 0ul
noextract inline_for_extraction let m3_a = U32.(m3_kAB +^ key_length)

noextract inline_for_extraction let state_B_kAB = 0ul
noextract inline_for_extraction let state_B_nB = U32.(state_B_kAB +^ key_length)

assume val new_key: (r: key) -> EXT unit
assume val new_host: (r: host) -> EXT unit
assume val new_nonce: (r: nonce) -> EXT unit

noextract let join3 (l1, l2, l3: (S.seq 'a & S.seq 'a & S.seq 'a))
    = S.(l1 @| l2 @| l3)

noextract let join4 (l1, l2, l3, l4: (S.seq 'a & S.seq 'a & S.seq 'a & S.seq 'a))
    = S.(l1 @| l2 @| l3 @| l4)

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
    memcpy kAS (B.sub state state1_A_kAS key_length)   key_length;
    memcpy b   (B.sub state state1_A_b   host_length)  host_length;
    memcpy nA  (B.sub state state1_A_nA  nonce_length) nonce_length;
    // m1
    memcpy a  (B.sub m1 m1_a  host_length)  host_length;
    memcpy b  (B.sub m1 m1_b  host_length)  host_length;
    memcpy nA (B.sub m1 m1_nA nonce_length) nonce_length;
    ()
#pop-options

let encrypt_pre (k: key) (p c: B.buffer U8.t) (l: U32.t{l `U32.gt` cipher_header_length}) (h: H.mem) =
    let open B in
    B.length p = U32.v U32.(l -^ cipher_header_length) /\
    B.length c = U32.v l /\
    live h k /\ live h p /\ live h c /\
    True

assume val encrypt:
    k: key ->
    p: B.buffer U8.t ->
    c: B.buffer U8.t ->
    l: U32.t{l `U32.gt` cipher_header_length} ->
    Stack unit
    (requires fun h ->
        let open B in
        encrypt_pre k p c l h /\
        disjoint c k /\ disjoint c p /\
        True)
    (ensures fun h0 _ h1 ->
        let open B in
        modifies (loc_buffer c) h0 h1 /\
        // plaintext_of and key_of
        True)

assume val decrypt:
    k: key ->
    c: B.buffer U8.t ->
    p: B.buffer U8.t ->
    l: U32.t{l `U32.gt` cipher_header_length} ->
    Stack bool
    (requires fun h ->
        let open B in
        encrypt_pre k p c l h /\
        disjoint p k /\ disjoint p c /\
        True)
    // (requires fun _ -> True)
    (ensures fun h0 b h1 ->
        let open B in
        modifies (loc_buffer p) h0 h1 /\
        // plaintext_of and key_of
        True)

noextract inline_for_extraction let nul = U8.uint_to_t 0

// This may not be feasible prove.
#push-options "--z3rlimit 60"
let generate_key_S (kAS kBS: key) (m1: m1t) (kAB: key) (m2: m2t) (a: host): Stack unit
    (requires fun h ->
        let open B in
        live h kAS /\ live h kBS /\ live h m1 /\ live h kAB /\ live h m2 /\ live h a /\
        disjoint m2 kAS /\ disjoint m2 kBS /\ disjoint m2 m1 /\ disjoint m2 kAB /\
        disjoint a kAS /\ disjoint a kBS /\ disjoint a m1 /\ disjoint a kAB /\
        disjoint a m2)
    (ensures fun h0 _ h1 ->
        let open M in
        // modifies (loc_union (loc_buffer m2) (loc_buffer a)) h0 h1 /\
        // TODO: Prove.
        True)
=
    push_frame();
    let open U32 in
    // m1
    memcpy (B.sub m1 m1_a host_length) a host_length;
    let b  = B.sub m1 m1_b  host_length in
    let nA = B.sub m1 m1_nA nonce_length in
    // m3
    let m3_p = B.alloca nul (m3_length -^ cipher_header_length) in
    memcpy kAB (B.sub m3_p m3_kAB key_length) key_length;
    memcpy a   (B.sub m3_p m3_a host_length)  host_length;
    // m2
    let m2_p = B.alloca nul (m2_length -^ cipher_header_length) in
    memcpy nA  (B.sub m2_p m2_nA nonce_length) nonce_length;
    memcpy kAB (B.sub m2_p m2_kAB key_length)  key_length;
    memcpy b   (B.sub m2_p m2_b host_length)   host_length;
    encrypt kBS m3_p (B.sub m2_p m2_m3 m3_length) m3_length;
    encrypt kAS m2_p m2 m2_length;
    pop_frame()
#pop-options

noextract inline_for_extraction let host_eq (b1: host) (b2: host): Stack bool
    (requires fun h ->
        let open B in
        live h b1 /\ live h b2)
    (ensures fun h0 r h1 ->
        let open B in
        modifies loc_none h0 h1 /\
        r <==> (B.as_seq h0 b1 `S.equal` B.as_seq h0 b2) /\
        True)
=
    assert (host_length = 6ul);
    let r0 = b1.(0ul) = b2.(0ul) in
    let r1 = b1.(1ul) = b2.(1ul) in
    let r2 = b1.(2ul) = b2.(2ul) in
    let r3 = b1.(3ul) = b2.(3ul) in
    let r4 = b1.(4ul) = b2.(4ul) in
    let r5 = b1.(5ul) = b2.(5ul) in
    r0 && r1 && r2 && r3 && r4 && r5

noextract inline_for_extraction let nonce_eq (b1: nonce) (b2: nonce): Stack bool
    (requires fun h ->
        let open B in
        live h b1 /\ live h b2)
    (ensures fun h0 r h1 ->
        let open B in
        modifies loc_none h0 h1 /\
        r <==> (B.as_seq h0 b1 `S.equal` B.as_seq h0 b2) /\
        True)
=
    assert (nonce_length = 24ul);
    let r0  = b1.( 0ul) = b2.( 0ul) in
    let r1  = b1.( 1ul) = b2.( 1ul) in
    let r2  = b1.( 2ul) = b2.( 2ul) in
    let r3  = b1.( 3ul) = b2.( 3ul) in
    let r4  = b1.( 4ul) = b2.( 4ul) in
    let r5  = b1.( 5ul) = b2.( 5ul) in
    let r6  = b1.( 6ul) = b2.( 6ul) in
    let r7  = b1.( 7ul) = b2.( 7ul) in
    let r8  = b1.( 8ul) = b2.( 8ul) in
    let r9  = b1.( 9ul) = b2.( 9ul) in
    let r10 = b1.(10ul) = b2.(10ul) in
    let r11 = b1.(11ul) = b2.(11ul) in
    let r12 = b1.(12ul) = b2.(12ul) in
    let r13 = b1.(13ul) = b2.(13ul) in
    let r14 = b1.(14ul) = b2.(14ul) in
    let r15 = b1.(15ul) = b2.(15ul) in
    let r16 = b1.(16ul) = b2.(16ul) in
    let r17 = b1.(17ul) = b2.(17ul) in
    let r18 = b1.(18ul) = b2.(18ul) in
    let r19 = b1.(19ul) = b2.(19ul) in
    let r20 = b1.(20ul) = b2.(20ul) in
    let r21 = b1.(21ul) = b2.(21ul) in
    let r22 = b1.(22ul) = b2.(22ul) in
    let r23 = b1.(23ul) = b2.(23ul) in
     r0 &&  r1 &&  r2 &&  r3 &&  r4 &&  r5 &&  r6 &&  r7 &&  r8 &&  r9 &&
    r10 && r11 && r12 && r13 && r14 && r15 && r16 && r17 && r18 && r19 &&
    r20 && r21 && r22 && r23

#push-options "--z3rlimit 30"
let handshake_A (state1: state1_At) (m2: m2t) (state2: state2_At) (m3: m3t): Stack bool
    (requires fun h ->
        let open B in
        live h state1 /\ live h m2 /\ live h state2 /\ live h m3 /\
        disjoint state2 state1 /\ disjoint state2 m2 /\
        disjoint m3 state1 /\ disjoint m3 m2 /\
        disjoint state2 m3)
    (ensures fun h0 _ h1 ->
        let open M in
        // modifies (loc_union (loc_buffer state2) (loc_buffer m3)) h0 h1 /\
        // TODO: Prove.
        True)
=
    push_frame();
    let open U32 in
    // state
    let kAS = B.sub state1 state1_A_kAS key_length in
    // m2
    let m2_p = B.alloca nul (m2_length -^ cipher_header_length) in
    let r = if decrypt kAS m2 m2_p m2_length then
        let b  = B.sub state1 state1_A_b  host_length in
        let nA = B.sub state1 state1_A_nA nonce_length in
        let b'  = B.sub m2_p m2_b  host_length in
        let nA' = B.sub m2_p m2_nA nonce_length in
        let eq_b = host_eq b b' in
        let eq_nA = nonce_eq nA nA' in
        if eq_b && eq_nA then (
            // state2
            memcpy (B.sub m2_p m2_kAB key_length) state2 key_length;
            // m3
            memcpy (B.sub m2_p m2_m3  m3_length)  m3 m3_length;
            true)
        else false
    else false in
    pop_frame();
    r
#pop-options

assume val dec: n: nonce -> Stack unit
    (requires fun h ->
        let open B in
        live h n)
    (ensures fun h0 _ h1 ->
        let open M in
        modifies (loc_buffer n) h0 h1 /\
        True)

#push-options "--z3rlimit 30"
let handshake_B (kBS: key) (m3: m3t) (nB: nonce) (state: state_Bt) (m4: m4t) (a: host): Stack bool
    (requires fun h ->
        let open B in
        live h kBS /\ live h m3 /\ live h nB /\ live h state /\ live h m4 /\ live h a /\
        disjoint state kBS /\ disjoint state m3 /\ disjoint state nB /\
        disjoint m4 kBS /\ disjoint m4 m3 /\ disjoint m4 nB /\
        disjoint a kBS /\ disjoint a m3 /\ disjoint a nB /\
        disjoint state m4 /\ disjoint state a /\ disjoint m4 a)
    (ensures fun h0 _ h1 ->
        let open M in
        // modifies (loc_union (loc_buffer state) (loc_buffer m4) (loc_buffer a)) h0 h1 /\
        // TODO: Prove.
        True)
=
    push_frame();
    let open U32 in
    // m3
    let m3_p = B.alloca nul (m3_length -^ cipher_header_length) in
    let r = if decrypt kBS m3 m3_p m3_length then (
        let kAB = B.sub m3_p m3_kAB key_length in
        // state
        memcpy kAB (B.sub state state_B_kAB key_length)   key_length;
        memcpy nB  (B.sub state state_B_nB  nonce_length) nonce_length;
        // m4
        encrypt kAB nB m4 m4_length;
        // a
        memcpy (B.sub m3_p m3_a host_length) a host_length;
        true)
    else false in
    pop_frame();
    r
#pop-options

#push-options "--z3rlimit 30"
let accept_A (state: state2_At) (m4: m4t) (kAB: key) (m5: m5t): Stack bool
    (requires fun h ->
        let open B in
        live h state /\ live h m4 /\ live h m5 /\ live h kAB /\
        disjoint kAB state /\ disjoint kAB m4 /\
        disjoint m5 state /\ disjoint m5 m4 /\
        disjoint kAB m5)
    (ensures fun h0 _ h1 ->
        let open M in
        modifies (loc_union (loc_buffer m5) (loc_buffer kAB)) h0 h1 /\
        // TODO: Prove.
        True)
=
    push_frame();
    let open U32 in
    // m4
    let m4_p = B.alloca nul (m4_length -^ cipher_header_length) in
    let r = if decrypt state m4 m4_p m4_length then (
        let nB = m4_p in
        dec nB;
        // kAB
        memcpy state kAB key_length;
        // m5
        encrypt kAB nB m5 m5_length;
        true)
    else false in
    pop_frame();
    r
#pop-options

#push-options "--z3rlimit 30"
let accept_B (state: state_Bt) (m5: m5t) (kAB: key): Stack bool
    (requires fun h ->
        let open B in
        live h state /\ live h m5 /\ live h kAB /\
        disjoint kAB state /\ disjoint kAB m5)
    (ensures fun h0 _ h1 ->
        let open M in
        // modifies (loc_buffer kAB) h0 h1 /\
        // TODO: Prove.
        True)
=
    push_frame();
    let open U32 in
    // m5
    let kAB' = B.sub state state_B_kAB key_length in
    let m5_p = B.alloca nul (m5_length -^ cipher_header_length) in
    let r = if decrypt kAB' m5 m5_p m5_length then (
        let nB  = B.sub state state_B_nB  nonce_length in
        let nB' = B.alloca nul nonce_length in
        memcpy nB nB' nonce_length;
        dec nB';
        // kAB
        if nonce_eq nB' m5_p then (
            memcpy kAB' kAB key_length;
            true)
        else false)
    else false in
    pop_frame();
    r
#pop-options

(*
type m3t = ciphertext (key & host)
type m2t =  ciphertext (nonce & key & host & m3t)
*)
noextract let joinCipher (v: Spec.m2t) =
    let _, t = v in
    let n, k, h, m3 = t in
    let _, tt = m3 in
    let inner_key, inner_host = tt in
    S.(n @| k @| h @|  inner_key @| inner_host)

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
