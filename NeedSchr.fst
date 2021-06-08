module NeedSchr

module U32 = FStar.UInt32
module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32
(*Need hacl for star*)
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open ST
open FStar.Pervasives
open U32
open FStar.Heap
open HS
open FStar.Set

assume type heap
assume val sel : #a:Type -> heap -> ref a -> Tot a
assume val upd : #a:Type -> heap -> ref a -> a -> Tot heap
assume val contains : #a:Type -> heap -> ref a -> Tot bool

noeq type key =
    | Key : r:rid
        -> k:ref int{frameOf k = r}
        -> key

noeq type ciphertext =
    | Ciphertext : r:rid
        -> msg:ref string{frameOf msg = r}
        -> k:key{includes r (Key?.r k)}
        -> ciphertext

noeq type nonce = 
    | Nonce : r:rid
        -> n:ref int {frameOf n = r}
        -> nonce

let mul (a b: U32.t) = a*%^b 

(*let yolo (a: nonce) = 
    sel h (nonce?.n) = 0*)
