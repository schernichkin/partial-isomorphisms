#!/usr/bin/env bash
set -xe
PIVER=$(cat partial-isomorphisms.cabal|grep '^version:'|head -1|awk '{print $2}')
PIDOCDIR=partial-isomorphisms-$PIVER-docs
stack haddock
rm -rf _release/$PIDOCDIR
mkdir -p _release
cp -r $(stack path --local-doc-root)/partial-isomorphisms-$PIVER _release/$PIDOCDIR
sed -i 's/href="\.\.\/\([^/]*\)\//href="..\/..\/\1\/docs\//g' _release/$PIDOCDIR/*.html
(cd _release && tar cvz --format=ustar -f $PIDOCDIR.tar.gz $PIDOCDIR)
curl -X PUT \
     -H 'Content-Type: application/x-tar' \
     -H 'Content-Encoding: gzip' \
     -u schernichkin \
     --data-binary "@_release/$PIDOCDIR.tar.gz" \
     "https://hackage.haskell.org/package/partial-isomorphisms-$PIVER/docs"