int a[];

void main() {
  a = malloc(sizeof(int)*3);
  free(a);
}
