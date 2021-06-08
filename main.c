// We always want assertions.
#undef NDEBUG

#include <stdio.h>
#include <assert.h>

#include "dist/impl/Impl_NeedSchr.h"

int main(){
    uint8_t a[HOST_LENGTH];
    Impl_NeedSchr_new_host(a);

    uint8_t b[HOST_LENGTH];
    Impl_NeedSchr_new_host(b);

    uint8_t kAS[KEY_LENGTH];
    Impl_NeedSchr_new_key(kAS);

    uint8_t kBS[KEY_LENGTH];
    Impl_NeedSchr_new_key(kBS);

    uint8_t nA[NONCE_LENGTH];
    Impl_NeedSchr_new_nonce(nA);

    uint8_t state1_A[STATE1_A_LENGTH];
    uint8_t m1[M1_LENGTH];
    Impl_NeedSchr_initiate_A(kAS, a, b, nA, state1_A, m1);
    // A -> S: (a, b, nA)
    uint8_t kAB[KEY_LENGTH];
    Impl_NeedSchr_new_key(kAB);

    uint8_t m2[M2_LENGTH];
    uint8_t a_S[HOST_LENGTH];
    Impl_NeedSchr_generate_key_S(kAS, kBS, m1, kAB, m2, a_S);

    assert(memcmp(a, a_S, HOST_LENGTH) == 0);

    // S -> A: { nA, kAB, b, { kAB, a }kBS }kAS
    uint8_t state2_A[STATE2_A_LENGTH];
    uint8_t m3[M3_LENGTH];
    assert(Impl_NeedSchr_handshake_A(state1_A, m2, state2_A, m3));

    // A -> B: { kAB, a }kBS
    uint8_t nB[NONCE_LENGTH];
    Impl_NeedSchr_new_nonce(nB);

    uint8_t state_B[STATE_B_LENGTH];
    uint8_t m4[M4_LENGTH];
    uint8_t a_B[HOST_LENGTH];
    assert(Impl_NeedSchr_handshake_B(kBS, m3, nB, state_B, m4, a_B));

    assert(memcmp(a, a_B, HOST_LENGTH) == 0);

    // B -> A: { nB }kAB
    uint8_t m5[M5_LENGTH];
    uint8_t kAB_A[KEY_LENGTH];
    assert(Impl_NeedSchr_accept_A(state2_A, m4, kAB_A, m5));

    // A -> B: { dec(nB) }kAB
    uint8_t kAB_B[KEY_LENGTH];
    assert(Impl_NeedSchr_accept_B(state_B, m5, kAB_B));

    assert(memcmp(kAB_A, kAB_B, KEY_LENGTH) == 0);
}
