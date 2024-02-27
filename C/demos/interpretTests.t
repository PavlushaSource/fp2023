  $ ./demoInterpret.exe << EOF
  > int factorial(int n) {
  >  if (n >= 1) {
  >   return n * factorial(n - 1);
  >  }
  >  else {
  >   return 1;
  >  }
  > }
  > int main() { 
  >  int n = 5;
  >  return factorial(n);
  > }
  > EOF
  120

  $ ./demoInterpret.exe << EOF
  >  int binarySearch(int a, int *array, int n) {
  >   int low = 0;
  >   int high = n - 1;
  >   int middle;
  >   while (low <= high) {
  >     middle = (low + high) / 2;
  >     if (a < array[middle] || a > array[middle]) {
  >       if (a < array[middle]) {
  >         high = middle - 1;
  >       } 
  >       else {
  >         low = middle + 1;
  >       }
  >     } 
  >     else {
  >       return middle;
  >     } 
  >   }
  >   return -1;
  > }
  > 
  > int main() {
  >   int array[5] = {3, 7, 10, 23, 100};
  >   return binarySearch(10, array, 5);
  > }
  > EOF
  2

  $ ./demoInterpret.exe << EOF
  > int main() {
  > int32_t i = 0;
  > int32_t j;
  > int32_t sum = 0;
  > while (i < 10) {
  >     j = 0;
  >     while (j < 10) {
  >         if (j == 5) {
  >             break;
  >         }
  >         sum = sum + 1;
  >         j = j + 1;
  >     }
  >     if (i == 5) {
  >         break;
  >     }
  >     i = i + 1;
  > }
  > return sum;
  > }
  > EOF
  30

  $ ./demoInterpret.exe << EOF
  > int memcpy(int8_t* source, int8_t* dst, int n) {
  >   int8_t i = 0;
  >   while (i < n) {
  >       dst[i] = source[i];
  >       i = i + 1;
  >   }
  >   return 0;
  > }
  > int main() {
  >   int8_t dst[4] = {0, 0, 0, 0};
  >   int32_t source[1] = {197121};
  >   memcpy(source, dst, 4);
  >   return dst[2];
  > }
  > EOF
  3

  $ ./demoInterpret.exe << EOF
  > int change(int32_t *pointer_a) {
  >   int32_t* pointer_a_2 = pointer_a;
  >   *pointer_a_2 = 100;
  >   return 0;
  > }
  > 
  > int main() {
  >   int32_t a = 20;
  >   change(&a);
  >   return a;
  > }
  > EOF
  100
