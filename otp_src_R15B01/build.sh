#!/bin/sh

#  build.sh
#  CouchDB
#
#  Created by Casey Marshall on 4/13/12.
#  Copyright (c) 2012 Memeo, Inc. All rights reserved.

set -ev
action=$1
test -z "$action" && action=build
case "$action" in
    build)
        test -f ${BUILT_PRODUCTS_DIR}/erlang/erlang-built && exit 0
        mkdir -p ${CONFIGURATION_TEMP_DIR}/otp_src_R15B01
        cd ${CONFIGURATION_TEMP_DIR}/otp_src_R15B01
        rm -rf otp_src_R15B01
        cp -r ${SRCROOT}/otp_src_R15B01/ .
        cd otp_src_R15B01
        CFLAGS="-O0" ./otp_src_R15B01/configure --prefix=${BUILT_PRODUCTS_DIR}/erlang --enable-kernel-poll --enable-threads --enable-dynamic-ssl-lib --enable-shared-zlib --enable-smp-support --enable-darwin-64bit --without-javac
        touch lib/wx/SKIP
        make -j8
        make install
        touch ${BUILT_PRODUCTS_DIR}/erlang/erlang-built
    ;;

    clean)
        make -C ${SRCROOT}/otp_src_R15B01 clean
        rm -rf ${BUILT_PRODUCTS_DIR}/erlang
    ;;

    *)
    ;;
esac