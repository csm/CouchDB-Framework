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
        test -f ${BUILT_PRODUCTS_DIR}/nspr/nspr-built && exit 0
        mkdir -p ${CONFIGURATION_TEMP_DIR}/nspr-build
        cd ${CONFIGURATION_TEMP_DIR}/nspr-build
        MACOSX_DEPLOYMENT_TARGET="10.6" CFLAGS="-arch i386" CXXFLAGS="-arch i386" LDFLAGS="-arch i386" ${SRCROOT}/nspr-4.8.9/mozilla/nsprpub/configure --prefix=${BUILT_PRODUCTS_DIR}/nspr --disable-64bit --enable-macos-target=10.6
        make -j8
        make install
        touch ${BUILT_PRODUCTS_DIR}/nspr/nspr-built
    ;;

    clean)
        rm -rf ${CONFIGURATION_TEMP_DIR}/nspr-build
        rm -rf ${BUILT_PRODUCTS_DIR}/nspr
    ;;

    *)
    ;;
esac