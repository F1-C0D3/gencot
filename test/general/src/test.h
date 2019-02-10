/**
 * \file ssl.h
 *
 * \brief SSL/TLS functions.
 */
/*
 *  Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */
#ifndef MBEDTLS_SSL_H
#define MBEDTLS_SSL_H

#if !defined(MBEDTLS_CONFIG_FILE)
#include "mbedtls/config.h"
#else
#include MBEDTLS_CONFIG_FILE
#endif

//#include "bignum.h"
#include "mbedtls/ecp.h"

#if defined(MBEDTLS_DEPRECATED_WARNING)
#warning "Record compression support via MBEDTLS_ZLIB_SUPPORT is deprecated and will be removed in the next major revision of the library"
#endif

/*
 * SSL Error codes
 */
#define MBEDTLS_ERR_SSL_FEATURE_UNAVAILABLE               -0x7080  /**< The requested feature is not available. */
#define MBEDTLS_ERR_SSL_BAD_INPUT_DATA                    -0x7100  /**< Bad input parameters to function. */

/*
 * Various constants
 */
#define MBEDTLS_SSL_MAJOR_VERSION_3             3
#define MBEDTLS_SSL_MINOR_VERSION_0             0   /*!< SSL v3.0 */

/*
 * Default range for DTLS retransmission timer value, in milliseconds.
 * RFC 6347 4.2.4.1 says from 1 second to 60 seconds.
 */
#define MBEDTLS_SSL_DTLS_TIMEOUT_DFL_MIN    1000
#define MBEDTLS_SSL_DTLS_TIMEOUT_DFL_MAX   60000

/*
 * Maximum fragment length in bytes,
 * determines the size of each of the two internal I/O buffers.
 */
#if !defined(MBEDTLS_SSL_MAX_CONTENT_LEN)
#define MBEDTLS_SSL_MAX_CONTENT_LEN         16384   /**< Size of the input / output buffer */
#endif

#if !defined(MBEDTLS_SSL_IN_CONTENT_LEN)
#define MBEDTLS_SSL_IN_CONTENT_LEN MBEDTLS_SSL_MAX_CONTENT_LEN
#endif


/* Dummy type used only for its size */
union mbedtls_ssl_premaster_secret
{
#if defined(MBEDTLS_KEY_EXCHANGE_RSA_ENABLED)
    unsigned char _pms_rsa[48];                         /* RFC 5246 8.1.1 */
#endif
#if defined(MBEDTLS_KEY_EXCHANGE_DHE_RSA_ENABLED)
    unsigned char _pms_dhm[MBEDTLS_MPI_MAX_SIZE];      /* RFC 5246 8.1.2 */
#endif
};

#define MBEDTLS_PREMASTER_SIZE     sizeof( union mbedtls_ssl_premaster_secret )

#ifdef __cplusplus
extern "C" {
#endif

/*
 * SSL state machine
 */
typedef enum
{
    MBEDTLS_SSL_HELLO_REQUEST,
    MBEDTLS_SSL_CLIENT_HELLO,
}
mbedtls_ssl_states;

/**
 * \brief          Callback type: send data on the network.
 *
 * \note           That callback may be either blocking or non-blocking.
 *
 * \param ctx      Context for the send callback (typically a file descriptor)
 * \param buf      Buffer holding the data to send
 * \param len      Length of the data to send
 *
 * \return         The callback must return the number of bytes sent if any,
 *                 or a non-zero error code.
 *                 If performing non-blocking I/O, \c MBEDTLS_ERR_SSL_WANT_WRITE
 *                 must be returned when the operation would block.
 *
 * \note           The callback is allowed to send fewer bytes than requested.
 *                 It must always return the number of bytes actually sent.
 */
typedef int mbedtls_ssl_send_t( void *ctx,
                                const unsigned char *buf,
                                size_t len );

/* Defined below */
typedef struct mbedtls_ssl_session mbedtls_ssl_session;
typedef struct mbedtls_ssl_context mbedtls_ssl_context;
typedef struct mbedtls_ssl_config  mbedtls_ssl_config;

/* Defined in ssl_internal.h */
typedef struct mbedtls_ssl_transform mbedtls_ssl_transform;
typedef struct mbedtls_ssl_handshake_params mbedtls_ssl_handshake_params;
typedef struct mbedtls_ssl_sig_hash_set_t mbedtls_ssl_sig_hash_set_t;
#if defined(MBEDTLS_X509_CRT_PARSE_C)
typedef struct mbedtls_ssl_key_cert mbedtls_ssl_key_cert;
#endif
#if defined(MBEDTLS_SSL_PROTO_DTLS)
typedef struct mbedtls_ssl_flight_item mbedtls_ssl_flight_item;
#endif

#if defined(MBEDTLS_SSL_ASYNC_PRIVATE)
/**
 * \brief           Callback type: start external signature operation.
 */
typedef int mbedtls_ssl_async_sign_t( mbedtls_ssl_context *ssl,
                                      const unsigned char *hash,
                                      size_t hash_len );

#endif /* MBEDTLS_SSL_ASYNC_PRIVATE */

/*
 * This structure is used for storing current session data.
 */
struct mbedtls_ssl_session
{
#if defined(MBEDTLS_HAVE_TIME)
#endif
    int ciphersuite;            /*!< chosen ciphersuite */
    size_t id_len;              /*!< session id length  */
    unsigned char id[32];       /*!< session identifier */
};

/**
 * SSL/TLS configuration to be shared between mbedtls_ssl_context structures.
 */
struct mbedtls_ssl_config
{
    /* Group items by size (largest first) to minimize padding overhead */

    /*
     * Pointers
     */

    const int *ciphersuite_list[4]; /*!< allowed ciphersuites per version   */

    /** Callback for printing debug output                                  */
    void (*f_dbg)(void *, int, const char *, int, const char *);
    void *p_dbg;                    /*!< context for the debug function     */

    /** Callback to customize X.509 certificate chain verification          */
    int (*f_vrfy)(void *, int, uint32_t *);
    void *p_vrfy;                   /*!< context for X.509 verify calllback */

#if defined(MBEDTLS_SSL_ASYNC_PRIVATE)
#if defined(MBEDTLS_X509_CRT_PARSE_C)
    mbedtls_ssl_async_sign_t *f_async_sign_start; /*!< start asynchronous signature operation */
#endif /* MBEDTLS_X509_CRT_PARSE_C */
#endif /* MBEDTLS_SSL_ASYNC_PRIVATE */

#if defined(MBEDTLS_DHM_C)
    mbedtls_mpi dhm_P;              /*!< prime modulus for DHM              */
#endif

#if defined(MBEDTLS_SSL_ALPN)
    const char **alpn_list;         /*!< ordered list of protocols          */
#endif

    /*
     * Flags (bitfields)
     */

    unsigned int endpoint : 1;      /*!< 0: client, 1: server               */
    unsigned int authmode : 2;      /*!< MBEDTLS_SSL_VERIFY_XXX             */
};


struct mbedtls_ssl_context
{
    const mbedtls_ssl_config *conf; /*!< configuration information          */

    /*
     * Miscellaneous
     */
    int state;                  /*!< SSL handshake: current state     */
};

#if defined(MBEDTLS_SSL_HW_RECORD_ACCEL)

#define MBEDTLS_SSL_CHANNEL_OUTBOUND    0
#define MBEDTLS_SSL_CHANNEL_INBOUND     1

extern int (*mbedtls_ssl_hw_record_init)(mbedtls_ssl_context *ssl,
                const unsigned char *key_enc, const unsigned char *key_dec,
                size_t maclen);
#endif /* MBEDTLS_SSL_HW_RECORD_ACCEL */

/**
 * \brief               Return the name of the ciphersuite associated with the
 *                      given ID
 *
 * \param ciphersuite_id SSL ciphersuite ID
 *
 * \return              a string containing the ciphersuite name
 */
const char *mbedtls_ssl_get_ciphersuite_name( const int ciphersuite_id );

/**
 * \brief               Return the ID of the ciphersuite associated with the
 *                      given name
 *
 * \param ciphersuite_name SSL ciphersuite name
 *
 * \return              the ID with the ciphersuite or 0 if not found
 */
int mbedtls_ssl_get_ciphersuite_id( const char *ciphersuite_name );

/**
 * \brief          Initialize an SSL context
 *                 Just makes the context ready for mbedtls_ssl_setup() or
 *                 mbedtls_ssl_free()
 *
 * \param ssl      SSL context
 */
void mbedtls_ssl_init( mbedtls_ssl_context *ssl );

/**
 * \brief          Set up an SSL context for use
 *
 */
int mbedtls_ssl_setup( mbedtls_ssl_context *ssl,
                       const mbedtls_ssl_config *conf );

#if defined(MBEDTLS_X509_CRT_PARSE_C)
/**
 * \brief          Set the verification callback (Optional).
 */
void mbedtls_ssl_conf_verify( mbedtls_ssl_config *conf,
                     int (*f_vrfy)(void *, int, uint32_t *),
                     void *p_vrfy );
#endif /* MBEDTLS_X509_CRT_PARSE_C */

/**
 * \brief          Set the underlying BIO callbacks for write, read and
 *                 read-with-timeout.
 */
void mbedtls_ssl_set_bio( mbedtls_ssl_context *ssl,
                          void *p_bio,
                          mbedtls_ssl_send_t *f_send );

typedef int mbedtls_ssl_cookie_write_t( void *ctx,
                                unsigned char **p, unsigned char *end,
                                const unsigned char *info, size_t ilen );


#if !defined(MBEDTLS_DEPRECATED_REMOVED)

#if defined(MBEDTLS_DEPRECATED_WARNING)
#define MBEDTLS_DEPRECATED    __attribute__((deprecated))
#else
#define MBEDTLS_DEPRECATED
#endif

/**
 * \brief          Set the Diffie-Hellman public P and G values,
 *                 read as hexadecimal strings (server-side only)
 *                 (Default values: MBEDTLS_DHM_RFC3526_MODP_2048_[PG])
 *
 * \param conf     SSL configuration
 * \param dhm_P    Diffie-Hellman-Merkle modulus
 * \param dhm_G    Diffie-Hellman-Merkle generator
 *
 * \deprecated     Superseded by \c mbedtls_ssl_conf_dh_param_bin.
 *
 * \return         0 if successful
 */
MBEDTLS_DEPRECATED int mbedtls_ssl_conf_dh_param( mbedtls_ssl_config *conf,
                                                  const char *dhm_P,
                                                  const char *dhm_G );

#endif /* MBEDTLS_DEPRECATED_REMOVED */

#ifdef __cplusplus
}
#endif

#endif /* ssl.h */
