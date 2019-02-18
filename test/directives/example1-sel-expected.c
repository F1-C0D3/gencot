# 1 "<stdin>"

#define SUPPORT_X

#if !defined(MBEDTLS_CONFIG_FILE)
#include "mbedtls/config.h"
#else
#include MBEDTLS_CONFIG_FILE
#endif

#if defined(MBEDTLS_SSL_TLS_C)

#if defined(MBEDTLS_PLATFORM_C)
#include "mbedtls/platform.h"
#elif defined(SUPPORT_X)

#else
#include <stdlib.h>
#define mbedtls_calloc    calloc
#define mbedtls_free      free
#endif

#if defined(SUPPORT_X)

#elif !defined(XXX)

#else

#endif

# 40 "<stdin>"
#include <string.h>

#define SSL_DONT_FORCE_FLUSH 0
#define SSL_FORCE_FLUSH      1

#ifdef MBEDTLS_ZLIB_SUPPORT
#define MBEDTLS_SSL_IN_BUFFER_LEN 5
#define MBEDTLS_SSL_OUT_BUFFER_LEN 10

#define MBEDTLS_SSL_COMPRESS_BUFFER_LEN (                               \
        ( MBEDTLS_SSL_IN_BUFFER_LEN > MBEDTLS_SSL_OUT_BUFFER_LEN )      \
        ? MBEDTLS_SSL_IN_BUFFER_LEN                                     \
        : MBEDTLS_SSL_OUT_BUFFER_LEN                                    \
        )
#endif

#undef SUPPORT_X
#if defined(MBEDTLS_SSL_PROTO_DTLS)














#endif

#endif

