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
        MACOSX_DEPLOYMENT_TARGET="10.6" CFLAGS="-arch i386" CXXFLAGS="-arch i386" LDFLAGS="-arch i386" ${SRCROOT}/icu/source/runConfigureICU MacOSX --enable-static --disable-shared --prefix=${BUILT_PRODUCTS_DIR}/icu --disable-extras --disable-icuio --disable-layout --disable-tests --disable-samples --with-library-bits=32
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