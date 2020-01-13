#include <stdio.h>
#include "cards.h"
#include "rank.h"

int main(void) {
  puts("Just a test:");
  print_card(card_from_num(42));
  puts("  is card no 42");
  print_card(card_from_letters('Q','d'));
  puts("  is diamonds queen");
  return 0;
}
 
