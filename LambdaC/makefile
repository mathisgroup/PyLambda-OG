PROG = lambda.so

CC	= gcc
CFLAGS   = -fPIC \
	      -shared
LIBS = 

FILES   = lambda.c \
	  utilities.c

OBJS    = lambda.o \
	  utilities.o 

$(PROG):  $(OBJS)
	  $(CC) -o $(PROG) $(CFLAGS) $(OBJS) $(LIBS)

all: $(PROG)

clean: 
	rm -f *.o *~ $(PROG) core
