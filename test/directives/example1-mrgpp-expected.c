1

3

#include "mbedtls/config.h"

#include MBEDTLS_CONFIG_FILE





#include "mbedtls/platform.h"

#ORIGIN 15 +
int something;
#ENDORIG 15 +
#include <stdlib.h>




#ORIGIN 18 +
#define mbedtls_calloc calloc
sembedtls_calloc: U32
sembedtls_calloc = mbedtls_calloc
#ENDORIG 18 +
#ORIGIN 19 +
#define mbedtls_free free
sembedtls_free: U32
sembedtls_free = mbedtls_free
#ENDORIG 19 +
#ORIGIN 23 +
int support = 5;
#ENDORIG 23 +

#ORIGIN 25 +
char support = 'c';
#ENDORIG 25 +
#ORIGIN 27 +
long long support;
#ENDORIG 27 +


#include <string.h>

#ORIGIN 43 +
#define SSL_FORCE_FLUSH 1
cogent_SSL_FORCE_FLUSH: U8
cogent_SSL_FORCE_FLUSH = SSL_FORCE_FLUSH
#ENDORIG 43 +
#ORIGIN 46 +
#define MBEDTLS_SSL_IN_BUFFER_LEN 5
sEMBEDTLS_SSL_IN_BUFFER_LEN: U8
sEMBEDTLS_SSL_IN_BUFFER_LEN = MBEDTLS_SSL_IN_BUFFER_LEN
#ENDORIG 46 +
#ORIGIN 47 +
#define MBEDTLS_SSL_OUT_BUFFER_LEN 10
sEMBEDTLS_SSL_OUT_BUFFER_LEN: U8
sEMBEDTLS_SSL_OUT_BUFFER_LEN = MBEDTLS_SSL_OUT_BUFFER_LEN
#ENDORIG 47 +
#ORIGIN 48 +
xxxx
#ENDORIG 48 +


#ORIGIN 49 +
#define MBEDTLS_SSL_COMPRESS_BUFFER_LEN ( \
        ( sEMBEDTLS_SSL_IN_BUFFER_LEN > sEMBEDTLS_SSL_OUT_BUFFER_LEN ) \
        ? sEMBEDTLS_SSL_IN_BUFFER_LEN \
        : sEMBEDTLS_SSL_OUT_BUFFER_LEN \
        )
sEMBEDTLS_SSL_COMPRESS_BUFFER_LEN: U32
sEMBEDTLS_SSL_COMPRESS_BUFFER_LEN = MBEDTLS_SSL_COMPRESS_BUFFER_LEN
#ENDORIG 53 +
#ORIGIN 59 +
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
#ENDORIG 70 +
 
