cd ~/lean && rm -rf rcpt_quadparabola rcpt_quadrangle
for p in quadparabola:f85c7bbdbf527c37b940d2331e6d720f01d221db quadrangle:4153ce0b11533a95060eb4f1a25e54708fa13875; do r=${p%%:*}; c=${p#*:}
 cd ~/lean && git clone -q https://github.com/jpbald93/$r rcpt_$r && cd rcpt_$r && git checkout -q $c && echo "== $r $(git rev-parse HEAD)" && mkdir -p .lake && ln -s ~/lean/clifford/.lake/packages .lake/packages && ~/lean/jl build > build.log 2>&1; echo "build rc=$?"; ~/lean/jl gate 2>&1 | tail -1; ~/lean/jl tamper 2>&1 | tail -1
 find . -name '*.lean' -not -path './.lake/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256 | cut -c1-16
done
echo RCPTDONE
