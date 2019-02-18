# 1 "<stdin>"
1
#define SUPPORT_X
3

#include "mbedtls/config.h"

#include MBEDTLS_CONFIG_FILE





#include "mbedtls/platform.h"

int something;

#include <stdlib.h>




#if defined(SUPPORT_X)
int support = 5;
#elif !defined(XXX)
char support = 'c';
#else
long long support;
#endif

# 40 "<stdin>"
#include <string.h>







xxxx







#undef SUPPORT_X


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




 
