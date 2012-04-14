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
        mkdir -p ${CONFIGURATION_TEMP_DIR}/js-build
        cd ${CONFIGURATION_TEMP_DIR}/js-build
        ${SRCROOT}/js-1.8.5/js/src/configure --prefix=${BUILT_PRODUCTS_DIR}/js --with-nspr-prefix=${BUILT_PRODUCTS_DIR}/nspr
        make -j8
        make install
        touch ${BUILT_PRODUCTS_DIR}/js/js-built
    ;;

    clean)
        rm -rf ${BUILT_PRODUCTS_DIR}/js
        rm -rf ${CONFIGURATION_TEMP_DIR}/js
    ;;
esac