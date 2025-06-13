CFLAGS=-O4 -g -DFLOAT_FLOW -Wall
BINDIR=bin
SOURCES = src/1.0/incremental.c
OBJECTS = $(SOURCES:.c=.o)
TARGET = incremental
CC=gcc

all: $(TARGET) 

clean:
	rm -f $(OBJECTS) $(TARGET) 

$(TARGET): $(OBJECTS) ${BINDIR}
	$(CC) $(CFLAGS) -o bin/$(TARGET) $(OBJECTS)

$(TARGET)_SIMPLE: 
	$(CC) $(CFLAGS) -DSIMPLE_PARAMETRIC -o bin/$(TARGET)_SIMPLE $(SOURCES)

$(TARGET)_LOWEST:
	$(CC) $(CFLAGS) -DLOWEST_LABEL -o bin/$(TARGET)_LOWEST $(SOURCES)

${BINDIR}/pseudo_par:
	${CC} ${CFLAGS} src/1.0/pseudopar.c -o ${BINDIR}/pseudo_par

${BINDIR}:
	mkdir ${BINDIR}	
