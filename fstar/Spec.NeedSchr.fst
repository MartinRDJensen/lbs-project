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
    let kAB = new_key () in
    let m2 = encrypt kBS (kAB, a) in
    let m1 = encrypt kAS (nA, kAB, b, m2) in
    // S -> A: { nA, kAB, b, { kAB, a }kBS }kAS
    let nA', kAB', b', m2' = decrypt kAS m1 in
    let _ = assert (nA' = nA) in
    let _ = assert (kAB' = kAB) in
    let _ = assert (b' = b) in
    let _ = assert (m2' = m2) in
    // A -> B: { kAB, a }kBS
    let kAB'', a'' = decrypt kBS m2' in
    let _ = assert (kAB'' = kAB) in
    let _ = assert (a'' = a) in
    let nB = new_nonce () in
    let m3 = encrypt kAB'' nB in
    // B -> A: { nB }kAB
    let nB' = decrypt kAB' m3 in
    let _ = assert (nB' = nB) in
    let m4 = encrypt kAB'' (dec nB') in
    // A -> B: { dec(nB) }kAB
    let nB'' = decrypt kAB' m4 in
    let _ = assert (nB'' = dec nB) in
    kAB
