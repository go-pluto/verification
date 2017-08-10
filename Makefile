.PHONY: download-crdt
download-crdt:
	wget -P thys/ https://www.isa-afp.org/release/afp-CRDT-current.tar.gz 
	tar -xvzf thys/afp-CRDT-current.tar.gz -C thys/

.PHONY: download-isabelle
download-isabelle:
	wget http://isabelle.in.tum.de/dist/Isabelle2016-1_app.tar.gz
	tar -xvzf Isabelle2016-1_app.tar.gz

.PHONY: build-docs
build-docs:
	Isabelle2016-1/bin/isabelle build -D ./thys/IMAP-CRDT/ -o browser_info -v IMAP-CRDT

