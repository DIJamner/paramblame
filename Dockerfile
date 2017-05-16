FROM ocaml/opam:debian-9_ocaml-4.03.0
ADD Makefile /paramblame/Makefile
ADD opam /paramblame/opam
ADD _oasis /paramblame/_oasis
ADD _tags /paramblame/_tags
WORKDIR /paramblame
USER opam
ADD *.ml* /paramblame/
ADD artifact /paramblame/artifact
RUN sudo chown -R opam /paramblame
ADD build.sh /paramblame/build.sh
RUN sudo -u opam bash ./build.sh
CMD ./test.native