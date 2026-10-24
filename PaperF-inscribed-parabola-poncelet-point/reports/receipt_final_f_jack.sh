export PATH=$HOME/.elan/bin:$PATH; cd ~ && rm -rf rcpt_quadparabola rcpt_quadrangle
for p in quadparabola:f85c7bbdbf527c37b940d2331e6d720f01d221db quadrangle:4153ce0b11533a95060eb4f1a25e54708fa13875; do r=${p%%:*}; c=${p#*:}
 cd ~ && git clone -q https://github.com/jpbald93/$r rcpt_$r && cd rcpt_$r && git checkout -q $c && echo "== $r $(git rev-parse HEAD)" && mkdir -p .lake && ln -s ~/barbier/.lake/packages .lake/packages && flock ~/l15jack.lock lake build > build.log 2>&1; echo "build rc=$?"; flock ~/l15jack.lock bash gate.sh 2>&1 | tail -1; flock ~/l15jack.lock bash tests/tamper.sh 2>&1 | tail -1
 find . -name '*.lean' -not -path './.lake/*' | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-16
done
echo RCPTDONE
