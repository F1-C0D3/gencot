# 1 "<stdin>"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "<stdin>"
# 1 "<mappings>"
# 1 "<stdin>"

_#define GENCOT_SUPPORT_X
# 18 "<stdin>"
_#define GENCOT_mbedtls_calloc calloc
_#define GENCOT_mbedtls_free free
# 40 "<stdin>"


_#define GENCOT_SSL_DONT_FORCE_FLUSH 0
_#define GENCOT_SSL_FORCE_FLUSH 1


_#define GENCOT_MBEDTLS_SSL_IN_BUFFER_LEN 5
_#define GENCOT_MBEDTLS_SSL_OUT_BUFFER_LEN 10

_#define GENCOT_MBEDTLS_SSL_COMPRESS_BUFFER_LEN ( \
        ( seMBEDTLS_SSL_IN_BUFFER_LEN > seMBEDTLS_SSL_OUT_BUFFER_LEN ) \
        ? seMBEDTLS_SSL_IN_BUFFER_LEN \
        : seMBEDTLS_SSL_OUT_BUFFER_LEN \
        )
