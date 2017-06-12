# all:
# 	ocamlopt.opt -c src/tgls_new.c

test:
	ocamlopt.opt -c src/tgls_new.c
	time ocamlopt.opt -c -pp '~/Desktop/reprocessing/node_modules/bs-platform/bin/refmt.exe -p binary' -impl src/tgls_new.re
	time ocamlopt.opt -ccopt -L  -ccopt /opt/X11/lib -ccopt -lGLESv2 tgls_new.o src/tgls_new.cmx
