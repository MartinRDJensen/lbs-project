module Spec.NeedSchr

module U32 = FStar.UInt32

open FStar.Pervasives

assume new type key: eqtype
assume new type host: eqtype
assume new type nonce: eqtype

type ciphertext 'a = (key & 'a)

let key_of (k,_:ciphertext 'a) = k
let plaintext_of (_,m:ciphertext 'a) = m

let encrypt (k:key) (m:'a) = (k, m)

let decrypt (k:key) (c:ciphertext 'a): Pure 'a
    (requires k = key_of c)
    (ensures fun r -> r == plaintext_of c)
=
    plaintext_of c

let encrypt_decrypt (k:key) (m:'a): Lemma
    (decrypt k (encrypt k m) == m) = ()

assume val new_key: unit -> EXT key
assume val new_nonce: unit -> EXT nonce

assume val dec: nonce -> nonce

// TODO: Turn individual steps into functions that correspond directly to functions in ProVerif.
let needham_schroeder (kAS kBS: key) (a b:host) =
    // A
    let nA = new_nonce () in
    // A -> S: (a, b, nA)
    let kAB_S = new_key () in
    let m2_S = encrypt kBS (kAB_S, a) in
    let m1 = encrypt kAS (nA, kAB_S, b, m2_S) in
    // S -> A: { nA, kAB, b, { kAB, a }kBS }kAS
    let nA', kAB_A, b_A, m2 = decrypt kAS m1 in
    let _ = assert (nA' = nA) in
    let _ = assert (kAB_A = kAB_S) in
    let _ = assert (b_A = b) in
    let _ = assert (m2 = m2_S) in
    // A -> B: { kAB, a }kBS
    let kAB_B, a_B = decrypt kBS m2 in
    let _ = assert (kAB_B = kAB_S) in
    let _ = assert (a_B = a) in
    let nB_A = new_nonce () in
    let m3 = encrypt kAB_B nB_A in
    // B -> A: { nB }kAB
    let nB_A = decrypt kAB_A m3 in
    let _ = assert (nB_A = nB_A) in
    let m4 = encrypt kAB_B (dec nB_A) in
    // A -> B: { dec(nB) }kAB
    let _ = assert (decrypt kAB_A m4 = dec nB_A) in
    kAB_S
