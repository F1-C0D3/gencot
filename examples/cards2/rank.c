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
