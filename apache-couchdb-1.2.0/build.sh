#!/bin/sh

#  build.sh
#  CouchDB
#
#  Created by Casey Marshall on 4/13/12.
#  Copyright (c) 2012 Memeo, Inc. All rights reserved.

set -e

action=$1
test -z "$action" && action=build
case "$action" in
    build)
        test -f ${BUILT_PRODUCTS_DIR}/apache-couchdb/apache-couchdb-built && exit 0
        # Set path so we pick up the right icu-config
        export PATH=${BUILT_PRODUCTS_DIR}/icu/bin:$PATH
        mkdir -p ${CONFIGURATION_TEMP_DIR}/apache-couchdb-build
        cd ${CONFIGURATION_TEMP_DIR}/apache-couchdb-build
        LIBS="-lstdc++" CPPFLAGS="-I${BUILT_PRODUCTS_DIR}/icu/include" ERL=${BUILT_PRODUCTS_DIR}/erlang/bin/erl ERLC=${BUILT_PRODUCTS_DIR}/erlang/bin/erlc ${SRCROOT}/apache-couchdb-1.2.0/configure --prefix=${BUILT_PRODUCTS_DIR}/apache-couchdb --with-js-include=${BUILT_PRODUCTS_DIR}/js/include --with-js-lib=${BUILT_PRODUCTS_DIR}/js/lib --with-erlang=${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/usr/include
        make -j8
        make install
        touch ${BUILT_PRODUCTS_DIR}/apache-couchdb/apache-couchdb-built
    ;;

    clean)
        rm -rf ${BUILT_PRODUCTS_DIR}/apache-couchdb
        rm -rf ${CONFIGURATION_TEMP_DIR}/apache-couchdb
    ;;

    *)
    ;;
esac