#include <stdio.h>
#include <stdlib.h>
#include "cards.h"
#include "rank.h"

const char * ranking_to_string(hand_ranking_t r) {
  switch (r)
    {
    case STRAIGHT_FLUSH: return "STRAIGHT_FLUSH";
    case FOUR_OF_A_KIND: return "FOUR_OF_A_KIND";
    case FULL_HOUSE: return "FULL_HOUSE";
    case FLUSH: return "FLUSH";
    case STRAIGHT: return "STRAIGHT";
    case THREE_OF_A_KIND: return "THREE_OF_A_KIND";
    case TWO_PAIR: return "TWO_PAIR";
    case PAIR: return "PAIR";
    case NOTHING: return "NOTHING";
    default: return "Invalid";
    }

}

char value_letter(card_t c) {

  char letter = 'x';
  if (c.value >= 2 && c.value <= 9) {
    letter = '0' + c.value;
    return letter;
  } else if (c.value > 9 && c.value <= 14) {

    switch (c.value){
    case 10: return '0';
    case 11: return 74;
    case 12: return 81;
    case 13: return 75;
    case 14: return 65;
    }
  }
  return letter;
}

char suit_letter(card_t c) {

  switch (c.suit){
  case SPADES: return 's';
  case HEARTS: return 'h';
  case DIAMONDS: return 'd';
  case CLUBS: return 'c';
  case NUM_SUITS: return 'x';
  }
  return 'x';

}

void print_card(card_t c) {
  putchar (value_letter(c));
  putchar (suit_letter(c));
}

card_t card_from_letters(char value_let, char suit_let) {
  card_t temp;
  int value = value_let - 48;
  int suit = suit_let;

  switch (value_let){
  case '0':  value = 10; break;
  case 'J': value = 11; break;
  case 'Q': value = 12; break;
  case 'K': value = 13; break;
  case 'A': value = 14; break;
  }
  switch (suit_let){
  case 's': suit = SPADES; break;
  case 'h': suit = HEARTS; break;
  case 'd': suit = DIAMONDS; break;
  case 'c': suit = CLUBS; break;
  }

  temp.value = value;
  temp.suit = suit;
  return temp;
}

card_t card_from_num(unsigned c) {

  if (c > 51 || c < 0){
    puts("Invalid value provided\n");
    exit(EXIT_FAILURE);
  }
  card_t temp;
  temp.value = c % 13 + 2;
  temp.suit = c / 13;
  return temp;
}
 
int main(void) {
  puts("Just a test:");
  print_card(card_from_num(42));
  puts("  is card no 42");
  print_card(card_from_letters('Q','d'));
  puts("  is diamonds queen");
  return 0;
}
