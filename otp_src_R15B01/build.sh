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
        MACOSX_DEPLOYMENT_TARGET="10.6" CFLAGS="-O0 -arch i386" ./configure --prefix=${BUILT_PRODUCTS_DIR}/erlang --enable-kernel-poll --enable-threads --enable-dynamic-ssl-lib --enable-shared-zlib --enable-smp-support --without-javac --disable-hipe
        touch lib/wx/SKIP
        make -j8
        make install
        # Now 64-bit version.
#        cd ${CONFIGURATION_TEMP_DIR}
#        rm -rf otp_src_R15B01
#        cp -r ${SRCROOT}/otp_src_R15B01 ${CONFIGURATION_TEMP_DIR}
#        cd otp_src_R15B01
#        for dir in `cat ${SRCROOT}/otp_src_R15B01/empty.dirs`
#        do
#            mkdir -p $dir
#        done
#        MACOSX_DEPLOYMENT_TARGET="10.6" CFLAGS="-O0" ./configure --prefix=${BUILT_PRODUCTS_DIR}/erlang_64 --enable-kernel-poll --enable-threads --enable-dynamic-ssl-lib --enable-shared-zlib --enable-smp-support --without-javac --disable-hipe --enable-darwin-64bit
#        touch lib/wx/SKIP
#        make -j8
#        make install
        # Combine the binaries together.
#        mkdir -p ${BUILT_PRODUCTS_DIR}/erlang
#        rsync -av --exclude lib/erlang/bin/ct_run --exclude lib/erlang/bin/dialyzer --exclude lib/erlang/bin/erlc --exclude lib/erlang/bin/escript --exclude lib/erlang/bin/run_erl --exclude lib/erlang/bin/to_erl --exclude lib/erlang/bin/typer --exclude lib/erlang/erts-5.9.1/bin/beam --exclude lib/erlang/erts-5.9.1/bin/beam.smp --exclude lib/erlang/erts-5.9.1/bin/child_setup --exclude lib/erlang/erts-5.9.1/bin/ct_run --exclude lib/erlang/erts-5.9.1/bin/dialyzer --exclude lib/erlang/erts-5.9.1/bin/dyn_erl --exclude lib/erlang/erts-5.9.1/bin/epmd --exclude lib/erlang/erts-5.9.1/bin/erlc --exclude lib/erlang/erts-5.9.1/bin/erlexec --exclude lib/erlang/erts-5.9.1/bin/escript --exclude lib/erlang/erts-5.9.1/bin/heart --exclude lib/erlang/erts-5.9.1/bin/inet_gethost --exclude lib/erlang/erts-5.9.1/bin/run_erl --exclude lib/erlang/erts-5.9.1/bin/to_erl --exclude lib/erlang/erts-5.9.1/bin/typer --exclude lib/erlang/lib/asn1-1.7/priv/lib/asn1_erl_nif.so --exclude lib/erlang/lib/crypto-2.1/priv/lib/crypto.so --exclude lib/erlang/lib/crypto-2.1/priv/obj/crypto.o --exclude lib/erlang/lib/erl_interface-3.7.7/bin/erl_call --exclude lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv.so --exclude lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv_mt.so --exclude lib/erlang/lib/odbc-2.10.12/priv/bin/odbcserver --exclude lib/erlang/lib/os_mon-2.2.9/priv/bin/memsup --exclude lib/erlang/lib/runtime_tools-1.8.8/priv/lib/dyntrace.so --exclude lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_file_drv.so --exclude lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_ip_drv.so --exclude lib/erlang/lib/runtime_tools-1.8.8/priv/obj/dyntrace.o --exclude lib/erlang/lib/tools-2.6.7/bin/emem ${BUILT_PRODUCTS_DIR}/erlang_64/* ${BUILT_PRODUCTS_DIR}/erlang
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/ct_run ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/ct_run -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/ct_run
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/dialyzer ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/dialyzer -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/dialyzer
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/erlc ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/erlc -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/erlc
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/escript ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/escript -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/escript
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/run_erl ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/run_erl -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/run_erl
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/to_erl ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/to_erl -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/to_erl
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/bin/typer ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/bin/typer -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/bin/typer
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/beam ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/beam -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/beam
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/beam.smp ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/beam.smp -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/beam.smp
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/child_setup ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/child_setup -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/child_setup
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/ct_run ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/ct_run -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/ct_run
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/dialyzer ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/dialyzer -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/dialyzer
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/dyn_erl ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/dyn_erl -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/dyn_erl
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/epmd ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/epmd -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/epmd
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/erlc ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/erlc -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/erlc
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/erlexec ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/erlexec -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/erlexec
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/escript ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/escript -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/escript
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/heart ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/heart -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/heart
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/inet_gethost ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/inet_gethost -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/inet_gethost
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/run_erl ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/run_erl -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/run_erl
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/to_erl ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/to_erl -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/to_erl
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/erts-5.9.1/bin/typer ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/erts-5.9.1/bin/typer -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/erts-5.9.1/bin/typer
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/asn1-1.7/priv/lib/asn1_erl_nif.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/asn1-1.7/priv/lib/asn1_erl_nif.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/asn1-1.7/priv/lib/asn1_erl_nif.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/crypto-2.1/priv/lib/crypto.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/crypto-2.1/priv/lib/crypto.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/crypto-2.1/priv/lib/crypto.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/crypto-2.1/priv/obj/crypto.o ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/crypto-2.1/priv/obj/crypto.o -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/crypto-2.1/priv/obj/crypto.o
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/erl_interface-3.7.7/bin/erl_call ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/erl_interface-3.7.7/bin/erl_call -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/erl_interface-3.7.7/bin/erl_call
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv_mt.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv_mt.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/megaco-3.16.0.1/priv/lib/megaco_flex_scanner_drv_mt.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/odbc-2.10.12/priv/bin/odbcserver ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/odbc-2.10.12/priv/bin/odbcserver -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/odbc-2.10.12/priv/bin/odbcserver
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/os_mon-2.2.9/priv/bin/memsup ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/os_mon-2.2.9/priv/bin/memsup -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/os_mon-2.2.9/priv/bin/memsup
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/dyntrace.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/dyntrace.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/dyntrace.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_file_drv.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_file_drv.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_file_drv.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_ip_drv.so ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_ip_drv.so -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/runtime_tools-1.8.8/priv/lib/trace_ip_drv.so
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/runtime_tools-1.8.8/priv/obj/dyntrace.o ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/runtime_tools-1.8.8/priv/obj/dyntrace.o -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/runtime_tools-1.8.8/priv/obj/dyntrace.o
#        lipo -create ${BUILT_PRODUCTS_DIR}/erlang_64/lib/erlang/lib/tools-2.6.7/bin/emem ${BUILT_PRODUCTS_DIR}/erlang_32/lib/erlang/lib/tools-2.6.7/bin/emem -output ${BUILT_PRODUCTS_DIR}/erlang/lib/erlang/lib/tools-2.6.7/bin/emem
        touch ${BUILT_PRODUCTS_DIR}/erlang/erlang-built
    ;;

    clean)
        rm -rf ${CONFIGURATION_TEMP_DIR}/otp_src_R15B01
        rm -rf ${BUILT_PRODUCTS_DIR}/erlang*
    ;;

    *)
    ;;
esac