default: hol

hol:
	Holmake -r -I src

clean:
	cd src && Holmake clean

.PHONY: default hol clean
