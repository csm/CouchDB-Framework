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
        mkdir -p ${CONFIGURATION_TEMP_DIR}
        cd ${CONFIGURATION_TEMP_DIR}
        rm -rf otp_src_R15B01
        cp -r ${SRCROOT}/otp_src_R15B01 ${CONFIGURATION_TEMP_DIR}
        cd otp_src_R15B01
        for dir in `cat ${SRCROOT}/otp_src_R15B01/empty.dirs`
        do
            mkdir -p $dir
        done
        CFLAGS="-O0" ./configure --prefix=${BUILT_PRODUCTS_DIR}/erlang --enable-kernel-poll --enable-threads --enable-dynamic-ssl-lib --enable-shared-zlib --enable-smp-support --enable-darwin-64bit --without-javac --disable-hipe
        touch lib/wx/SKIP
        make
        make install
        touch ${BUILT_PRODUCTS_DIR}/erlang/erlang-built
    ;;

    clean)
        rm -rf ${CONFIGURATION_TEMP_DIR}/otp_src_R15B01
        rm -rf ${BUILT_PRODUCTS_DIR}/erlang
    ;;

    *)
    ;;
esac