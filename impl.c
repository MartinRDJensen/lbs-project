#include "dist/impl/Impl_NeedSchr.h"

#include <Hacl_NaCl.h>
#include <Lib_RandomBuffer_System.h>

#include <stdlib.h>

void Impl_NeedSchr_new_key(uint8_t *r){
    Lib_RandomBuffer_System_crypto_random(r, KEY_LENGTH);
}

void Impl_NeedSchr_new_host(uint8_t *r){
    Lib_RandomBuffer_System_crypto_random(r, HOST_LENGTH);
}

void Impl_NeedSchr_new_nonce(uint8_t *r){
    Lib_RandomBuffer_System_crypto_random(r, NONCE_LENGTH);
}

void Impl_NeedSchr_encrypt(uint8_t *k, uint8_t *p, uint8_t *c, uint32_t l){
    // We prefix ciphertext with nonce.
    Impl_NeedSchr_new_nonce(c);

    if(Hacl_NaCl_crypto_secretbox_easy(c+NONCE_LENGTH, p, l-CIPHER_HEADER_LENGTH, c, k) != 0){
        // This should never happen.
        abort();
    }
}

bool Impl_NeedSchr_decrypt(uint8_t *k, uint8_t *c, uint8_t *p, uint32_t l){
    return Hacl_NaCl_crypto_secretbox_open_easy(p, c+NONCE_LENGTH, l-NONCE_LENGTH, c, k) == 0;
}

void Impl_NeedSchr_dec(uint8_t *n){
    for(size_t i = 0;i < NONCE_LENGTH;++i){
        if(n[i]-- != 0){
            break;
        }
    }
}
