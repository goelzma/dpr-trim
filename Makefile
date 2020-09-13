all: dpr-trim lpr-check

dpr-trim: dpr-trim.c
	gcc dpr-trim.c -O2 -o dpr-trim

lpr-check: lpr-check.c
	gcc lpr-check.c -O2 -o lpr-check

clean:
	rm dpr-trim lpr-check
