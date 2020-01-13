/* Ranks enumeration */
#ifndef RANK_H
#define RANK_H

typedef enum hand_ranking {
  STRAIGHT_FLUSH,
  FOUR_OF_A_KIND,
  FULL_HOUSE,
  FLUSH,
  STRAIGHT,
  THREE_OF_A_KIND,
  TWO_PAIR,
  PAIR,
  NOTHING
} hand_ranking_t;

const char * ranking_to_string(hand_ranking_t r) ;

#endif /* RANK_H */
 
