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
        test -f ${BUILT_PRODUCTS_DIR}/icu/icu-built && exit 0
        mkdir -p ${CONFIGURATION_TEMP_DIR}/icu-build
        cd ${CONFIGURATION_TEMP_DIR}/icu-build
        ${SRCROOT}/icu/source/runConfigureICU MacOSX --enable-static --disable-shared --prefix=${BUILT_PRODUCTS_DIR}/icu
        make -j8
        make install
        touch ${BUILT_PRODUCTS_DIR}/icu/icu-built
    ;;

    clean)
        rm -rf ${CONFIGIRATION_TEMP_DIR}/icu-build
        rm -rf ${BUILT_PRODUCTS_DIR}/icu
    ;;

    *)
    ;;
esac