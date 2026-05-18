#include <elfutils/libdwfl.h>

int main(void)
{
Dwfl *dwfl = dwfl_begin(NULL);
(void)dwfl;
return 0;
}
