/* Cards constants and data types */
#ifndef CARD_H
#define CARD_H

// Card values
#define VALUE_ACE 14
#define VALUE_KING 13
#define VALUE_QUEEN 12
#define VALUE_JACK 11

typedef enum {
  SPADES,
  HEARTS,
  DIAMONDS,
  CLUBS,
  NUM_SUITS
} suit_t;

struct card_tag {
  suit_t suit;
  unsigned value;
};
typedef struct card_tag card_t;

/* Create a card from a number between 1 and 51 */
card_t card_from_num(unsigned c);

/* Return the letter specifying the card value.
 * The result is either a digit ('0' for a ten)
 * or one of the letters 'J', 'Q', 'K', 'A'
 */
char value_letter(card_t c);

/* Return the letter specifying the card suit.
 * The result is one of 's', 'h', 'd', 'c'.
 */
char suit_letter(card_t c);

/* Print the two-letter code for a card. */ 
void print_card(card_t c);

/* Create a card from its two-letter code. */
card_t card_from_letters(char value_let, char suit_let);

#endif /* CARD_H */
 
