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
        test -f ${BUILT_PRODUCTS_DIR}/js/js-built && exit 0
        # First build i386
        mkdir -p ${CONFIGURATION_TEMP_DIR}/js-build-32
        cd ${CONFIGURATION_TEMP_DIR}/js-build-32
        MACOSX_DEPLOYMENT_TARGET="10.6" AR="ar" CFLAGS="-arch i386" CXXFLAGS="-arch i386" LDFLAGS="-arch i386" ${SRCROOT}/js-1.8.5/js/src/configure --prefix=${BUILT_PRODUCTS_DIR}/js --with-nspr-prefix=${BUILT_PRODUCTS_DIR}/nspr --disable-md --target=i386-apple-darwin10.0.0 --disable-shared-js
        make -j8
        make install
        # Now build x86_64
#        mkdir -p ${CONFIGURATION_TEMP_DIR}/js-build-64
#        cd ${CONFIGURATION_TEMP_DIR}/js-build-64
#        MACOSX_DEPLOYMENT_TARGET="10.6" AR="ar" CC="gcc -m64" CXX="g++ -m64" CFLAGS="-arch x86_64" CXXFLAGS="-arch x86_64" LDFLAGS="-arch x86_64" ${SRCROOT}/js-1.8.5/js/src/configure --prefix=${BUILT_PRODUCTS_DIR}/js-64 --with-nspr-prefix=${BUILT_PRODUCTS_DIR}/nspr --disable-md --target=x86_64-apple-darwin10.0.0 --disable-shared-js
#        make -j8
#        make install
        # Combine previous results into fat binaries.
#        mkdir -p ${BUILT_PRODUCTS_DIR}/js
#        mkdir -p ${BUILT_PRODUCTS_DIR}/js/bin
#        mkdir -p ${BUILT_PRODUCTS_DIR}/js/include
#        mkdir -p ${BUILT_PRODUCTS_DIR}/js/lib
#        lipo -create ${BUILT_PRODUCTS_DIR}/js-32/lib/libmozjs185-1.0.a ${BUILT_PRODUCTS_DIR}/js-64/lib/libmozjs185-1.0.a -output ${BUILT_PRODUCTS_DIR}/js/lib/libmozjs185-1.0.a 
#        sed 's/js-64/js/g' < ${BUILT_PRODUCTS_DIR}/js-64/bin/js-config > ${BUILT_PRODUCTS_DIR}/js/bin/js-config
#        cp -r ${BUILT_PRODUCTS_DIR}/js-64/include/* ${BUILT_PRODUCTS_DIR}/js/include/
        touch ${BUILT_PRODUCTS_DIR}/js/js-built
    ;;

    clean)
        rm -rf ${BUILT_PRODUCTS_DIR}/js
        rm -rf ${CONFIGURATION_TEMP_DIR}/js
#        rm -rf ${CONFIGURATION_TEMP_DIR}/js-32
#        rm -rf ${CONFIGURATION_TEMP_DIR}/js-64
    ;;
esac