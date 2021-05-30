module Spec.NeedSchr

module U32 = FStar.UInt32

open FStar.Pervasives

assume new type key: eqtype
assume new type host: eqtype
assume new type nonce: eqtype

type ciphertext 'a = (key & 'a)

let key_of (k, _: ciphertext 'a) = k
let plaintext_of (_, m: ciphertext 'a) = m

let encrypt (k: key) (m: 'a) = (k, m)

let decrypt (k: key) (c: ciphertext 'a): option 'a =
    if k = key_of c then Some (plaintext_of c) else None

let encrypt_decrypt (k: key) (m: 'a): Lemma
    (decrypt k (encrypt k m) == Some m) = ()

assume val new_key: unit -> EXT key
assume val new_nonce: unit -> EXT nonce

assume val dec: nonce -> nonce

type m1t = (host & host & nonce)
type m3t = ciphertext (key & host)
type m2t = ciphertext (nonce & key & host & m3t)
type m4t = ciphertext nonce
type m5t = ciphertext nonce

type state1_At = (key & host & nonce)
type state2_At = key

type state1_Bt = (key & nonce)


let initiate_A (kAS: key) (a b: host) (nA: nonce): state1_At & m1t =
    ((kAS, b, nA), (a, b, nA))

let generate_key_S (kAS kBS: key) (a, b, nA: m1t) (kAB: key): m2t & host =
    encrypt kAS (nA, kAB, b, encrypt kBS (kAB, a)), a


let handshake_A (kAS, b, nA: state1_At) (m2: m2t): option (state2_At & m3t) =
    match decrypt kAS m2 with
    | None -> None
    | Some (nA', kAB, b', m3) ->
    if nA' = nA && b' = b
    then Some (kAB, m3)
    else None

let handshake_B (kBS: key) (m3: m3t) (nB: nonce): option (state1_Bt & m4t & host) =
    match decrypt kBS m3 with
    | None -> None
    | Some (kAB, a) ->
    Some ((kAB, nB), encrypt kAB nB, a)

let accept_A (kAB: state2_At) (m4: m4t): option (key & m5t) =
    match decrypt kAB m4 with
    | None -> None
    | Some nB ->
    Some (kAB, encrypt kAB (dec nB))

let accept_B (kAB, nB: state1_Bt) (m5: m5t): option key =
    match decrypt kAB m5 with
    | None -> None
    | Some nB' ->
    if dec nB = nB'
    then Some kAB
    else None

let needham_schroeder (kAS kBS: key) (a b: host) =
    // A
    let state1_A, m1 = initiate_A kAS a b (new_nonce ()) in
    // A -> S: (a, b, nA)
    let m2, a_S = generate_key_S kAS kBS m1 (new_key ()) in
    let _ = assert (a_S = a) in
    // S -> A: { nA, kAB, b, { kAB, a }kBS }kAS
    match handshake_A state1_A m2 with
    | Some (state2_A, m3) ->
    // A -> B: { kAB, a }kBS
    match handshake_B kBS m3 (new_nonce ()) with
    | Some (state1_B, m4, a_B) ->
    let _ = assert (a_B = a) in
    // B -> A: { nB }kAB
    match accept_A state2_A m4 with
    | Some (kAB_A, m5) ->
    // A -> B: { dec(nB) }kAB
    match accept_B state1_B m5 with
    | Some kAB_B ->
    let _ = assert (kAB_A = kAB_B) in
    ()
