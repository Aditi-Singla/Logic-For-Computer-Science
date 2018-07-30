#! /bin/bash

if [ "$#" == 2 ]; then
	cd src/
    sml run.sml ../"$1" ../"$2"
    rm lcs.grm.* lcs.lex.*
else
    echo "Illegal number of parameters ($#)"
fi
