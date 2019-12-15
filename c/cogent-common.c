// These are functions which are defined as abstract in 
// gum/common/common.cogent in the Cogent library.

u32 u64_to_u32 (u64 x) {
    return (u32)x;
}
u16 u64_to_u16(u64 x)
{
    return (u16)x;
}
u8 u32_to_u8 (u32 x) {
    return (u8)x;
}
u16 u32_to_u16 (u32 x) {
    return (u16)x;
}
u8 u16_to_u8 (u16 x) {
    return (u8)x;
}
extern int rand(void);
u32 random_u32 (unit_t x) {
    return rand();
}
