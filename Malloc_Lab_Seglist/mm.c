/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "8team",
    /* First member's full name */
    "Park Yuju",
    /* First member's email address */
    "yooju000326@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void *place(void *bp, size_t allocated_size);
static void *extend_heap(size_t words);

static void insert_node(void *bp);
static void delete_node(void *bp);
static int find_index(size_t size);

// Basic constants and macros
#define WSIZE               4                                                       // word = 4 byte
#define DSIZE               8                                                       // double word = 8 byte
#define CHUNKSIZE           (1 << 12)                                               // chunk size = 2^12 = 4096
#define SEGSIZE             20                                                      // seg_list size

#define MAX(x, y)           ((x) > (y) ? (x) : (y))                                 // x와 y 중 큰 값을 반환

// Pack a size and allocated bit into a word
#define PACK(size, alloc)   ((size) | (alloc))                                      // 크기 비트와 할당 비트를 통합해 header 및 footer에 저장할 수 있는 값 리턴

// Read and write a word at address p
#define GET(p)              (*(unsigned int *)(p))                                  // p가 참조하는 word를 읽어서 리턴 ((void*)라서 type casting 필요)
#define PUT(p, val)         (*(unsigned int *)(p) = (val))                          // p가 가리키는 word에 val 저장

// Read the size and allocated fields from address p
#define GET_SIZE(p)         (GET(p) & ~0x7)                                         // 사이즈 (뒤에 세자리 없어짐 -> 할당 여부와 무관한 사이즈를 반환)
#define GET_ALLOC(p)        (GET(p) & 0x1)                                          // 할당 여부 (마지막 한자리, 즉 할당 여부만 가지고 옴)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp)            ((char *)(bp) - WSIZE)                                  // 해당 블록의 header 주소를 반환 (payload 시작점인 bp에서 헤더 크기인 1 word를 뺀 값)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)             // 해당 블록의 footer 주소를 반환 (payload 시작점인 bp에서 블록 사이즈를 더한 뒤 2 word를 뺀 값)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))       // 다음 블록의 bp를 반환 (현재 bp에서 해당 블록의 크기를 더해준 값)
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))       // 이전 블록의 bp를 반환 (현재 bp에서 이전 블록의 크기를 빼준 값 -> DSIZE를 빼야 이전 블록의 정보를 가져올 수 있음!!)

/* single word (4) or double word (8) alignment */
// 정렬할 크기
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT
* - 입력된 size에 ALIGNMENT-1(111)을 더함
* - 0x7: 0000 0111 ~0x7: 1111 1000
* - & 연산자로 마지막 세자리를 0으로 바꿈
* -> size에 가장 가까운 8배수 생성
*/
#define ALIGN(size)         (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))

// **Explicit**
#define PRED_FREEP(bp)      (*(void **)(bp))                                        // 이전 가용 블록의 주소
#define SUCC_FREEP(bp)      (*(void **)(bp + WSIZE))                                // 다음 가용 블록의 주소

// 추가 변수 선언
static char *heap_listp = NULL;             // 메모리 힙의 시작 주소
void *seg_free_lists[SEGSIZE + 1];          // Segregated List 선언
// static char *next_listp[SEGSIZE + 1];

/* 
 * mm_init - initialize the malloc package.
 * - 초기 힙 영역을 확보하고 블록 생성하는 함수
 * - 할당기를 초기화하고 성공이면 0, 아니면 -1 리턴
 * - sbrk 함수를 호출하여 힙 영역 확보
 * - 프롤로그 블록: header, footer로 구성된 8 byte 할당 블록 
 * - 에필로그 블록: header로 구성된 0 byte 할당 블록
 */
int mm_init(void)
{
    for (int i = 0; i <= SEGSIZE; i++)                                  // Seg_list 초기화
    {
        seg_free_lists[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)               // 오류 발생 시 return -1
        return -1;

    PUT(heap_listp, 0);                                                 // Padding (8의 배수로 정렬하기 위해 패딩 블록 할당)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));                      // Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));                      // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));                          // Epilogue Header

    heap_listp += DSIZE;                                                // Prologue의 Footer와 Epilogue의 Header 사이에 포인터 위치

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)                         // CHUNK SIZE를 워드 단위로 환산해서 brk 확장
        return -1;
    
    return 0;
}



/*
* extend_heap - brk 포인터로 힙 영역을 확장하는 함수 (확장 단위는 CHUNK SIZE)
* - mm_init에서 초기 힙 영역을 확보했다면, 블록이 추가될 때 힙 영역을 확장해주는 역할
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;       // 워드 사이즈가 홀수라면 1을 더하고 짝수라면 그대로 WSIZE를 곱해서 사이즈 변환
    if ((bp = mem_sbrk(size)) == (void *)-1)                        // mem_sbrk로 힙 확보가 가능한지 여부를 체크
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));                                   // Block Header -> free(0) 설정
    PUT(FTRP(bp), PACK(size, 0));                                   // Block Footer -> free(0) 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                           // New Epilogue Header

    return coalesce(bp);                                            // 블록 연결 함수 호출
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *     요청한 사이즈만큼 메모리 블록을 가용 블록으로 확보하고 해당 payload 주소값을 리턴하는 함수
 */ 
void *mm_malloc(size_t size)
{
    size_t allocated_size;      // 블록 사이즈 조정
    size_t extend_size;         // heap에 맞는 fit이 없다면 확장하기 위한 사이즈
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)                                                      // 할당할 크기가 8 byte보다 작으면 allocated size에 16 byte를 담음
        allocated_size = 2 * DSIZE;
    
    else                                                                    // 할당할 크기가 8 byte보다 크면 allocated size를 8의 배수로 맞춰줘야 함
        allocated_size = ALIGN(size + DSIZE);                               // (할당할 크기 + 8 bytes (Header + Footer))를 8의 배수로 맞춰주는 작업
    
    if ((bp = find_fit(allocated_size)) != NULL)                            // find_fit 함수로 할당된 크기를 넣을 공간이 있는지 체크
    {
        place(bp, allocated_size);                                          // 가능하다면 분할 후 할당
        return bp;
    }

    extend_size = MAX(allocated_size, CHUNKSIZE);                           // 넣을 공간이 없다면, 새 가용블록으로 힙을 확장
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL)                    // 확장할 공간이 없다면 NULL 반환
        return NULL;
    
    place(bp, allocated_size);                                              // 확장이 됐다면, 공간을 할당하고 분할
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));           // 해당 블록의 사이즈 저장

    PUT(HDRP(bp), PACK(size, 0));               // 해당 블록의 Header -> free(0) 설정
    PUT(FTRP(bp), PACK(size, 0));               // 해당 블록의 Footer -> free(0) 설정
    coalesce(bp);                               // free 블록 연결 함수 호출
}


/*
* coalesce - 가용 블록 병합 함수
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: prev 할당 불가(1) & next 할당 불가(1)
    // Case 2: prev 할당 불가(1) & next 할당 가능(0) 
    if (prev_alloc && !next_alloc)
    {
        delete_node(NEXT_BLKP(bp));                 // 다음 블록을 리스트에서 삭제

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      // 현재 블록 사이즈에 다음 블록 사이즈를 더함
        PUT(HDRP(bp), PACK(size, 0));               // 현재 블록의 Header에 새로운 사이즈와 free(0) 설정
        PUT(FTRP(bp), PACK(size, 0));               // 현재 블록의 Footer에 새로운 사이즈와 free(0) 설정
    }

    // Case 3: prev 할당 가능(0) & next 할당 불가(1)
    else if (!prev_alloc && next_alloc)
    {
        delete_node(PREV_BLKP(bp));                 // 이전 블록을 리스트에서 삭제

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 현재 블록 사이즈에 이전 블록 사이즈를 더함
        bp = PREV_BLKP(bp);                         // bp를 이전 블록의 위치로 변경
        PUT(HDRP(bp), PACK(size, 0));               // 현재 블록의 Header에 새로운 사이즈와 free(0) 설정
        PUT(FTRP(bp), PACK(size, 0));               // 현재 블록의 Footer에 새로운 사이즈와 free(0) 설정
        
    }

    // Case 4: prev 할당 가능(0) & next 할당 가능(0)
    else if (!prev_alloc && !next_alloc)
    {
        delete_node(PREV_BLKP(bp));                                                 // 이전 블록을 리스트에서 삭제
        delete_node(NEXT_BLKP(bp));                                                 // 다음 블록을 리스트에서 삭제

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));      // 현재 블록 사이즈에 이전 블록 사이즈와 다음 블록 사이즈를 더함
        bp = PREV_BLKP(bp);                                                         // bp를 이전 블록의 위치로 변경
        PUT(HDRP(bp), PACK(size, 0));                                               // 현재 블록의 Header에 새로운 사이즈와 free(0) 설정
        PUT(FTRP(bp), PACK(size, 0));                                               // 현재 블록의 Footer에 새로운 사이즈와 free(0) 설정
        
    }
    insert_node(bp);                                                                // 병합된 블록을 list에 추가
    return bp;
}


/*
* place - 확보된 데이터 블록에 실제로 데이터 사이즈를 반영해서 할당 처리하는 함수
* - 위치와 사이즈를 인자로 받아서 영역 낭비를 최소화
*/
static void *place(void *bp, size_t allocated_size)
{
    size_t curr_size = GET_SIZE(HDRP(bp));
    delete_node(bp);      // 현재 블록 삭제

    // Case 1. 남는 부분이 최소 블록 크기(16 bytes) 이상일 때 -> 블록 분할
    if ((curr_size - allocated_size) >= (2 * DSIZE))            // 남는 블록이 최소 블록 크기(16 bytes) 이상일 때
    {
        PUT(HDRP(bp), PACK(allocated_size, 1));                 // Header -> size와 allocated(1) 설정
        PUT(FTRP(bp), PACK(allocated_size, 1));                 // Footer -> size와 allocated(1) 설정
        bp = NEXT_BLKP(bp);                                     // bp 위치를 다음 블록 위치로 갱신

        // 블록 분할
        PUT(HDRP(bp), PACK(curr_size - allocated_size, 0));     // 남은 공간의 Header -> 남는 size와 free(0) 설정
        PUT(FTRP(bp), PACK(curr_size - allocated_size, 0));     // 남은 공간의 Footer -> 남는 size와 free(0) 설정

        insert_node(bp);                                        // 분할된 (남은 가용) 블록을 free list에 삽입
    }

    // Case 2. 남는 부분이 최소 블록 크기(16 bytes) 미만일 때 -> 블록 분할 필요 X
    else
    {
        PUT(HDRP(bp), PACK(curr_size, 1));                      // 분할할 필요가 없다면, 그냥 할당
        PUT(FTRP(bp), PACK(curr_size, 1));                      // 남는 가용 블록이 없으므로 insert_node 호출할 필요 없음
    }
    return bp;
}


/*
* find_fit - 할당할 블록을 찾는 함수
* - Segregated List에서 알맞은 인덱스를 찾아서 가용 블록 탐색
*/

// First Fit (secs: 0.005350)
static void *find_fit(size_t asize)
{
    char *bp;
    int index = find_index(asize);
    
    for (int i = index; i <= SEGSIZE; i++)                                  
    {
        for (bp = seg_free_lists[i]; bp != NULL; bp = SUCC_FREEP(bp))       // 해당 인덱스의 리스트에서 적합한 가용 블록을 탐색하는 과정
        {
            if (GET_SIZE(HDRP(bp)) >= asize)                                // 크기가 맞는 블록을 찾으면
                return bp;                                                  // bp 반환
        }
    }
    return NULL;    // 알맞은 크기가 없다면 NULL 반환
}

// Best Fit (secs: 0.006705)
// static void *find_fit(size_t asize)
// {
//     char *best_fit_bp = NULL;               // 가장 작은 적합한 블록
//     size_t min_diff = __INT_MAX__;          // 가장 작은 크기 차이값을 저장하는 변수
//     int index = find_index(asize);          // 요청한 크기에 대한 인덱스

//     for (int i = index; i <= SEGSIZE; i++)                                  
//     {
//         // 현재 segregated list에서 적합한 블록 탐색
//         for (char *bp = seg_free_lists[i]; bp != NULL; bp = SUCC_FREEP(bp))       
//         {
//             if (GET_SIZE(HDRP(bp)) >= asize)                                
//             {
//                 size_t diff = GET_SIZE(HDRP(bp)) - asize;

//                 if (diff < min_diff) 
//                 {
//                     best_fit_bp = bp;       // 현재 블록을 가장 작은 적합 블록으로 설정
//                     min_diff = diff;        // 최소 차이 업데이트
//                 }
//             }
//         }
//     }
    
//     return best_fit_bp;
// }

// Next Fit -> next_listp를 업데이트 하다 보니 든 생각.. 어차피 LIFO 방식이라 First Fit이랑 다른거 없음.. (즉, 의미없는 짓이었다..ㅎㅎ)
// static void *find_fit(size_t size) 
// {
//     // Next Fit을 이용하여 할당할 블록을 찾음
//     char *bp;
//     int index = find_index(size);

//     if (next_listp[index] == NULL)
//         next_listp[index] = seg_free_lists[index];

//     for (bp = next_listp[index]; GET_SIZE(HDRP(bp)) > 0; bp = SUCC_FREEP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
//         {
//             next_listp[index] = bp;
//             return bp;
//         }
//     }

//     for (bp = heap_listp; HDRP(bp) != HDRP(next_listp[index]); bp = SUCC_FREEP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
//             return bp;
//     }

//     return NULL;
// }


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * - 메모리 재할당 함수
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;                        // 새 메모리 블록에 복사해야 할 데이터의 크기
    
//     newptr = mm_malloc(size);               // 요청한 사이즈만큼 블록 할당
//     if (newptr == NULL)
//         return NULL;
    
//     copySize = GET_SIZE(HDRP(oldptr));      // 이전 블록 사이즈를 copySize에 저장
    
//     if (size < copySize)                    // 요청한 size가 원래 크기보다 작다면,
//         copySize = size;                    // 기존 메모리 블록에서 일부만 복사해야 하므로 copySize를 요청한 크기로 설정
    
//     memcpy(newptr, oldptr, copySize);       // 이전 블록에서 copySize만큼의 데이터를 새 블록에 복사
//     mm_free(oldptr);                        // 기존 블록 free
//     return newptr;                                          
// }

/*
* New realloc 함수!!
* - 기존의 함수가 무조건 새로운 메모리를 할당했다면, 변형된 realloc 함수에서는 두가지 경우를 걸러줌으로써 자원 활용도를 높인다.
* - 1. 원래 사이즈가 새롭게 할당된 사이즈보다 클 때 -> 블록 분할
* - 2. 원래 사이즈보다 새롭게 할당된 사이즈가 더 클 때 -> 뒷 블록 체크해서 블록 병합
* - >> 그렇다면.. 이전 블록은 왜 체크를 안하는가? -> payload를 복사해줘야 하기 때문에 비효율적임!!
* - 44 (util) + 40 (thru) = 84/100 -> (realloc 변경 후) 50 (util) + 40 (thru) = 90/100
*/ 
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0) 
    {
        mm_free(ptr);
        return NULL; 
    }

    if (ptr == NULL) 
        return mm_malloc(size);                                             // ptr이 NULL이면 새로운 메모리 할당

    void *oldptr = ptr;                                                     // 기존의 메모리 주소 저장
    void *newptr = oldptr;                                                  // newptr에 oldptr 저장 
    size_t old_size = GET_SIZE(HDRP(oldptr));                               // 원래 사이즈 
    size_t allocated_size = ALIGN(size + DSIZE);                            // + DSIZE (Header + Footer)

    if (old_size >= allocated_size)                                         // Case 1: 기존 블록의 크기가 새로운 사이즈보다 클 때
    {
        if (old_size - allocated_size >= 2 * DSIZE)                         // 나머지 크기가 최소 블록 크기보다 크다면                   
        {
            PUT(HDRP(oldptr), PACK(allocated_size, 1));                     // 블록 분할
            PUT(FTRP(oldptr), PACK(allocated_size, 1));
            oldptr = NEXT_BLKP(oldptr);
            PUT(HDRP(oldptr), PACK(old_size - allocated_size, 0));
            PUT(FTRP(oldptr), PACK(old_size - allocated_size, 0));
            insert_node(oldptr);                                            // 리스트에 남은 블록 추가
        }
        return newptr;
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));                 // 다음 블록의 할당 여부
    size_t combined_next = old_size + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));    // 현재 블록과 다음 블록을 합친 크기

    if (!next_alloc && combined_next >= allocated_size)                     // Case 2: 다음 블록이 가용 상태이고 combined_size가 할당해야 할 크기보다 크다면
    {
        delete_node(NEXT_BLKP(oldptr));                                     // 다음 블록 리스트에서 삭제
        PUT(HDRP(oldptr), PACK(combined_next, 1));                          // 가용 블록 합체
        PUT(FTRP(oldptr), PACK(combined_next, 1));
        return newptr;
    }

    newptr = mm_malloc(size);                                               // 위 조건이 충족되지 않으면 새로운 메모리 블록 할당
    if (!newptr) 
        return NULL;

    memmove(newptr, oldptr, old_size - DSIZE);                              // 예전 블록에서 새 블록으로 데이터 복사
    mm_free(oldptr);                                                        // 예전 블록 메모리 해제
    return newptr;
}


/*
* Segregated List
* - 다수의 가용 리스트를 유지하며, 각각의 리스트는 거의 동일한 크기의 블록들을 저장
* - 모든 가능한 블록 크기를 동일 클래스의 집합들로 분리하는 방식
* - 블록의 크기 단위는 2의 n제곱 단위로 한다.
*/

// Seg_List Index를 찾는 함수
static int find_index(size_t size)
{
    int index = 0;

    /* 
    * Index를 찾는 방법!!
    * - size가 분할이 가능하다는 것은 shift 연산이 가능하다는 뜻
    * - shift 연산이 불가능할 때까지 size / 2를 계산해서 index를 하나씩 올려준다.
    * - 2의 n제곱으로 분리해서 리스트를 관리하는 방식
    */
    while ((index < SEGSIZE - 1) && (size > 1))     
    {
        size >>= 1;
        index++;
    }
    return index;
}

// Seg_list에 노드를 삽입하는 함수
static void insert_node(void *bp)
{
    int index = find_index(GET_SIZE(HDRP(bp)));                 // 리스트의 index
    
    // Case 1: 비어있는 리스트에 추가하는 경우
    if (seg_free_lists[index] == NULL)                          
    {
        PRED_FREEP(bp) = NULL;                                  // bp의 전임자는 NULL
        SUCC_FREEP(bp) = NULL;                                  // bp의 후임자는 NULL
    }

    // Case 2: 그 외
    else
    {
        PRED_FREEP(bp) = NULL;                                  // bp의 전임자는 NULL
        SUCC_FREEP(bp) = seg_free_lists[index];                 // 후임자는 기존의 첫번째 블록
        PRED_FREEP(seg_free_lists[index]) = bp;                 // 양방향 연결
    }
    seg_free_lists[index] = bp;                                 // 리스트 포인터를 bp로 변경
}

// Seg_list에서 노드를 삭제하는 함수
static void delete_node(void *bp)
{
    int index = find_index(GET_SIZE(HDRP(bp)));                 // 리스트의 index

    if (seg_free_lists[index] == bp)                            
    {
        // Case 1: 리스트의 유일한 블록을 삭제하는 경우
        if (SUCC_FREEP(bp) == NULL)                             
            seg_free_lists[index] = NULL;                       // 리스트 포인터 NULL 처리

        // Case 2: 리스트의 첫번째 블록을 삭제하는 경우
        else                                                    
        {
            PRED_FREEP(SUCC_FREEP(bp)) = NULL;                  // 후임자의 앞 주소 NULL 처리
            seg_free_lists[index] = SUCC_FREEP(bp);             // 리스트 포인터는 후임자로 설정
        }
    }

    else    
    {
        // Case 3: 리스트의 마지막 블록을 삭제하는 경우
        if (SUCC_FREEP(bp) == NULL)                             
            SUCC_FREEP(PRED_FREEP(bp)) = NULL;                  // 전임자의 뒷 주소 NULL 처리

        // Case 4: 중간에 위치한 블록을 삭제하는 경우
        else                                                    
        {    
            PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);        // 후임자의 앞 주소를 전임자로 설정
            SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);        // 전임자의 뒷 주소를 후임자로 설정
        }
    }
}