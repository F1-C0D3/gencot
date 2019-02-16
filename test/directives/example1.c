1
#define SUPPORT_X
3
#if !defined(MBEDTLS_CONFIG_FILE)
#include "mbedtls/config.h"
#else
#include MBEDTLS_CONFIG_FILE
#endif

#if defined(MBEDTLS_SSL_TLS_C)

#if defined(MBEDTLS_PLATFORM_C)
#include "mbedtls/platform.h"
#elif defined(SUPPORT_X)
int something;
#else
#include <stdlib.h>
#define mbedtls_calloc    calloc
#define mbedtls_free      free
#endif

#if defined(SUPPORT_X)
int support = 5;
#elif !defined(XXX)
char support = 'c';
#else
long long support;
#endif

# 40 "<stdin>"
#include <string.h>

#define SSL_DONT_FORCE_FLUSH 0
#define SSL_FORCE_FLUSH      1

#ifdef MBEDTLS_ZLIB_SUPPORT
xxxx
#define MBEDTLS_SSL_COMPRESS_BUFFER_LEN (                               \
        ( MBEDTLS_SSL_IN_BUFFER_LEN > MBEDTLS_SSL_OUT_BUFFER_LEN )      \
        ? MBEDTLS_SSL_IN_BUFFER_LEN                                     \
        : MBEDTLS_SSL_OUT_BUFFER_LEN                                    \
        )
#endif

#undef SUPPORT_X
#if defined(MBEDTLS_SSL_PROTO_DTLS)

static void ssl_buffering_free( mbedtls_ssl_context *ssl );
static void ssl_buffering_free_slot( mbedtls_ssl_context *ssl,
                                     uint8_t slot );
static size_t ssl_get_maximum_datagram_size( mbedtls_ssl_context const *ssl )
{
    size_t mtu = ssl_get_current_mtu( ssl );

    if( mtu != 0 && mtu < MBEDTLS_SSL_OUT_BUFFER_LEN )
        return( mtu );

    return( MBEDTLS_SSL_OUT_BUFFER_LEN );
}

#endif

#endif
 
