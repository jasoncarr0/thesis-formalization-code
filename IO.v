Inductive io_evt :=
| write : bool -> io_evt
| read : bool -> io_evt
.
