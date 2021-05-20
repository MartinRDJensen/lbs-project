module Test

module U32 = FStar.UInt32

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST
open LowStar.BufferOps

let mul (a b: U32.t) = let open U32 in a *%^ b

let on_the_heap (): ST UInt32.t
    (requires fun _ -> True)
    (ensures fun _ _ _ -> True)
=
    let b = B.malloc HyperStack.root 0ul 1ul in
    // b.(0ul) <- 32ul;
    // let r = b.(0ul) in
    B.free b;
    42ul

// let foo () =
//     let a = on_the_heap () in
//     assert(a = 42ul)

let bar (a:U32.t & U32.t) =
    let b,c = a in
    b
