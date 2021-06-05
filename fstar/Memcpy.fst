module Memcpy

module U32 = FStar.UInt32

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open LowStar.BufferOps

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
