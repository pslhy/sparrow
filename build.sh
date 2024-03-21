#!/bin/bash
set -e

export OPAMYES=1

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
SPARROW_OPAM_SWITCH=sparrow-"$OCAML_VERSION"+flambda
SPARROW_OPAM_SWITCH_OPTION="--package=ocaml-variants.${OCAML_VERSION}+options,ocaml-option-flambda"
opam init --reinit --bare --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$SPARROW_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done
if [ "$switch_exists" = "no" ]; then
  opam switch create $SPARROW_OPAM_SWITCH_OPTION $SPARROW_OPAM_SWITCH
else
  opam switch $SPARROW_OPAM_SWITCH
fi

eval $(SHELL=bash opam config env --switch=$SPARROW_OPAM_SWITCH)
echo -e "\e[31m[NOTE]\e[0m If you are not a sudo user, press Ctrl+D and skip installing system libraries. Contact the sysadmin, if they are not installed."
opam install apron clangml stdint || echo "Skip system library install"
opam pin add cil https://github.com/prosyslab/cil.git -n
opam pin add claml https://github.com/prosyslab/claml.git -n
opam pin add sparrow . -n
opam install -j $NCPU sparrow --deps-only
opam pin remove sparrow
make
