/*
 * File:        Python control for ECE 4760 Final Project: Ms PIC-MAN
 *             
 * 
 * sprintf(tft_str_buffer,"%d", score); //print new score
   tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
 * 
 * Authors:     Melissa Alvarez, Grace Ding, Kat Nelms
 * Adapted from code written by Bruce Land
 * 
 * For use with Sean Carroll's Big Board
 * http://people.ece.cornell.edu/land/courses/ece4760/PIC32/target_board.html
 * Target PIC:  PIC32MX250F128B
 * 
 * This code instantiates threads to communicate events from a Python
 * control interface and WASD user input. The goal of the lab is to program a 
 * simplified version of the classic arcade game Ms. PAC-MAN. Main features:
 * "START" screen displayed on TFT until start is pressed on the python GUI
 * Gameplay follows original 28x36 tile grid, each tile is 8x8 pixels.
 * Characters are displayed as a tile, and Ms. PICMAN moves at 11 tiles/sec

 * Start the python script or this program in either order
 * Typing anything in the Text input line causes the PIC to echo it into the receive window.
 *   Typing a command of the form "h" will echo back the form of the other commands
 * Checking the reset_enable, then clicking RESET PIC does the expected IF the circuit is connected
 */
// =============================================
// NOTE!! -- to use serial spawned functions
// you MUST EDIT config_1_3_2 to
// (1) uncomment the line -- #define use_uart_serial
// (2) SET the baud rate to match the PC terminal
// =============================================
////////////////////////////////////
// clock AND protoThreads configure!
// You MUST check this file!
#include "config_1_3_2.h"
// threading library
#include "pt_cornell_1_3_2_python.h"
#include <math.h>

////////////////////////////////////
// graphics libraries
// SPI channel 1 connections to TFT
#include "tft_master.h"
#include "tft_gfx.h"

////////////////////////////////////
//including the header files for kats funcs
#include "picman_funcs.h"
#include <stdlib.h>

//test comment for grace :)
//test comment for grace part 2 :)
//test comment for alvin :)
//test comment for alvin p 2 :)

// === INITIALIZE VARIABLES ==================================================

// -------- timer stuff ----------------------------------------------------
// pic is 240 pixels x 320 pixels, scale is appropriate
// pg 162 of pic32 manual, timer period is an int  
int TIMEOUT = 800000;// For ISR, but only if we get to adding music
int TIMEOUT4 = 40000000/40000; // = 1000 msec so the 16bit isr triggered 1 per sec

// The scatter/chase timer gets reset whenever a life is lost or a level is completed,
// and it is paused when frighten mode is triggered
// At the start of a level or after losing a life, ghosts emerge from the ghost 
// pen already in the first of the four scatter modes.
// scatter mode lasts 7s for instance 1,2 and 5 s for instance 3,4
int chaseTimer;  //switch to scatter mode once chase timer is above 20s, 4x per level
int frightTimer; //triggered when PICMAN eats Big Dots
char isStart;    //flag set once start button pressed on Python GUI
int begin_time, check_time; //begin used in timer thread, check is to turn on LED as long as we meet animation requirement
int global_dotCounter, PdotCounter, IdotCounter, CdotCounter; // these are all for ghost logic 
int global_ghost_timer;
int ghost_dot_counter;


// -------- character animation stuff ---------------------------------------
int direction;      //takes in WASD or arrow key input to change PICMAN motion
short xPacman =120; //initial pacman position stored as x,y pixel coords on tft
short yPacman =228;
short xBlinky = 120; //blinky starts just above pen, in scatter mode
short yBlinky = 132;
short xPinky = 120;
short yPinky = 156;
short xInky = 105;
short yInky = 156;
short xClyde = 137;
short yClyde = 156;
char ghostArray[4]={2,0,0,0};//blinky,pinky,inky,clyde
                             //0->in pen, 1->chase, 2->scatter, 3->frightened
int ghostCounters[3];//pinky,inky,clyde
char prevState[4]; //store ghost state so that when they come out of frighten mode, they return to chase or scatter 
int Bdirection = 2; //blinky's current direction. ghosts all initially move initially left 
int Pdirection = 2; //pinky's current direction
int Idirection = 2; // inky's current direction
int Cdirection = 2; // clyde. what a baller. does his own shit yk 
int prevDirection;  //stores pacmans previous direction in the event user tries to change direction into dead space
int bDirectionNext=2;   
int prevBDirection=2; //blinky
int prevPDirection; //pinky
int prevIDirection; //inky
int prevCDirection; //CLYDE we stan
int oppBDirection;  //store direction opposite to Blinky's current direction, useful bc ghosts cannot reverse
int oppPDirection;  //pinky
int oppIDirection;  //inky
int oppCDirection;  //clyde, loml
int P_xtarget;      //ghost target tiles, updated every animation loop based on picmans position
int P_ytarget;      //Blnky's target tile is picman and we just didnt create a separate variable 
int I_xtarget;
int I_ytarget;
int C_xtarget;
int C_ytarget;
short xTarget[4];
short yTarget[4];

//ghost mode stuff
int ghostsEaten = 0;
char isFrightened = 0; // 0 is not frightened, 1 is scary
char isChase=0;
char isScatter=1;
int seed_counter;
int ghostColors[4]={ILI9340_RED,ILI9340_PINK,ILI9340_CYAN,ILI9340_ORANGE};
int ghostColorsInit[4]={ILI9340_RED,ILI9340_PINK,ILI9340_CYAN,ILI9340_ORANGE};

//lost life, game over, new level etc
int i; int ii; int jj; //because for loops r everywhere
int score;
int lives = 3;
int flashFlag = 0; // if collision: if high, plot picman, if low, plot background color
int flashNum = 0; //keep track of how many times picman is flashed after collision,stop at 4x    
float flashCounter = 0; // to slow down animation speed of picman death
int collisionFlag = 0; //set to high when a collision happens to pause characters
int gameOverFlag = 0; //seems redundant bc we already have isStart but useful for plotting end of game, new game stuff
int numLevels, bug256flag; //how many levels have been cleared so far. Max? like 3 maybe? 
int dotsMunched = 0; // maze is 244 dots, used when level is complete
static int fruitxtile  = (120-8)/8; //tile that the fruit is fixed, used to update dots array
static int fruitytile = (179 - 16)/8;  
int fruitflag, fruitCounter, numFruit;


// ogdots array exists to reset dots when the game is over but PIC not reset
const char map[36][28]={ //hard code dead space and legal spaceTILES oof
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
    {0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
    {0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
    {0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
    {0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,1,1,1,1,1,1,1,1,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,0,0,0,0,0},
    {1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1},
    {0,0,0,0,0,0,1,0,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,1,1,1,1,1,1,1,1,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,0},
    {0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
    {0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
    {0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
    {0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
    {0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
    {0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
    }; //ew 
char dots[36][28] = { //hard code which legal space tiles have dots 
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,2,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,2,0},  
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
{0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
{0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
{0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,2,1,1,0,0,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,0,0,1,1,2,0}, 
{0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
{0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
{0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
{0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
{0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
};
char ogdots[36][28] = { //hard code which legal space tiles have dots 
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,2,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,2,0},  
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
{0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
{0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
{0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
{0,2,1,1,0,0,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,0,0,1,1,2,0}, 
{0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
{0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
{0,1,1,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,0,0,1,1,1,1,1,1,0},
{0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
{0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
{0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
}; 
char intersect_check[36][28] ={ 
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,4,1,1,1,1,4,1,1,1,1,1,4,0,0,4,1,1,1,1,1,4,1,1,1,1,4,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0}, 
    {0,4,1,1,1,1,4,1,1,4,1,1,4,1,1,4,1,1,4,1,1,4,1,1,1,1,4,0},
    {0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0},
    {0,4,1,1,1,1,4,0,0,4,1,1,4,0,0,4,1,1,4,0,0,4,1,1,1,1,4,0},
    {0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,4,1,1,4,1,1,4,1,1,4,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,0,0,0,0,0},
    {1,1,1,1,1,1,4,1,1,4,0,1,1,1,1,1,1,0,4,1,1,4,1,1,1,1,1,1},
    {0,0,0,0,0,0,1,0,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,4,1,1,1,1,1,1,1,1,4,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0},
    {0,4,1,1,1,1,4,1,1,4,1,1,4,0,0,4,1,1,4,1,1,4,1,1,1,1,4,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0},
    {0,4,1,4,0,0,4,1,1,4,1,1,4,1,1,4,1,1,4,1,1,4,0,0,4,1,4,0},
    {0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
    {0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0},
    {0,4,1,4,1,1,4,0,0,4,1,1,4,0,0,4,1,1,4,0,0,4,1,1,4,1,4,0},
    {0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
    {0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0},
    {0,4,1,1,1,1,1,1,1,1,1,1,1,1,1,4,1,1,1,1,1,1,1,1,1,1,4,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
    }; //ew 

char prevGhostDir[4]={2,2,2,2};
char currGhostDir[4]={2,2,2,2};
char nextGhostDir[4]={2,2,2,2};
char oppGhostDir[4] = {4,4,4,4};
char  frightStart[4] = {0, 0, 0, 0};
short xGhostPos[4]={120,120,104,136};
short yGhostPos[4]={132,156,156,156};
short xGhostPosInit[4]={120,120,104,136};
short yGhostPosInit[4]={132,156,156,156};
short currXGhostPos[4];
short currYGhostPos[4];
short currXGhostTile[4];
short currYGhostTile[4];

////////////////////////////////////
// === print a line on TFT =====================================================
// function written by Bruce 
char tft_str_buffer[60];
// SEE 
// http://people.ece.cornell.edu/land/courses/ece4760/PIC32/index_TFT_display.html
// for details
void tft_printLine(int line_number, int indent, char* print_buffer, short text_color, short back_color, short char_size){
    // print_buffer is the string to print
    int v_pos, h_pos;
    char_size = (char_size>0)? char_size : 1 ;
    //
    v_pos = line_number * 8 * char_size ;
    h_pos = indent * 6 * char_size ;
    // erase the pixels
    //tft_fillRoundRect(0, v_pos, 239, 8, 1, back_color);// x,y,w,h,radius,color
    tft_setTextColor2(text_color, back_color); 
    tft_setCursor(h_pos, v_pos);
    tft_setTextSize(char_size);
    tft_writeString(print_buffer);
}


//== PICMAN NOISES ISR ===========================================
// USE DAC TO OUTPUT GAME SOUND EFFECTS
// NOTE left timer 2 and 3 are chained into one 32 bit timer
// bits 0-15 are timer 2, 16-31 timer 3
void __ISR(_TIMER_3_VECTOR, ipl2) Timer3Handler(void){
    // you MUST clear the ISR flag
    mT3ClearIntFlag(); 
        
}

// second ISR, not for any particular purpose yet
void __ISR(_TIMER_4_VECTOR, ipl2) Timer4Handler(void) {
	mT4ClearIntFlag(); // you MUST clear the ISR flag
   
}// end 16bit ISR

// === Timer Thread: CONTROLS GHOST MODES n FRUIT ==============================
// update a 1 second tick counter
static PT_THREAD (protothread_timer(struct pt *pt))
{
    PT_BEGIN(pt);
   
    while(1) {
        PT_YIELD_TIME_msec(1000); // yield time 1 second
        // chase timers reset after pacman loses a life
        // ghosts reverse directions for mode changes EXCEPT when returning from frighten mode
        if (isStart==1 && isFrightened == 0){ //if game is started via GUI and ghosts are not in frightened mode
            //0->in pen, 1->chase, 2->scatter, 3->frightened
            chaseTimer++; //increment timer to keep track of how long we've been in chase mode
            // ONLY increments if not in frightened mode !! nice 
            
            global_ghost_timer++;
            
            int i;
            if (chaseTimer<7){ //ghosts start in scatter mode, first scatter lasts 7 s
                for (i=0;i<4;i++){ // for all four ghosts
                    if (ghostArray[i]!=0){ //if ghost is not in monster pen
                        ghostArray[i]=2;   //ghosts start in scatter
                    }
                }
                isScatter=1;
                isChase=0;
            }
            else if (chaseTimer<27){ //go to chase mode after scatter1 for 7s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghost is not in monster pen
                        ghostArray[i]=1;   //change ghosts back to chase
                    }
                }
                isScatter=0;
                isChase=1;
            }
            else if (chaseTimer<34){ //scatter2 for 7s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen
                        ghostArray[i]=2;   //change ghosts from chase to scatter2
                    }
                }
                isScatter=1;
                isChase=0;
            }
            else if (chaseTimer<54){ //chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen 
                        ghostArray[i]=1;   //change ghosts back to chase
                    }
                }
                isScatter=0;
                isChase=1;
            }
            else if (chaseTimer<59){ //scatter3 for 5s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ // if ghosts not in monster pen
                        ghostArray[i]=2;   //scatter3
                    }
                }
                isScatter=1;
                isChase=0;
            }
            else if (chaseTimer<79){       //chase mode for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ // if ghosts not in monster pen
                        ghostArray[i]=1;   //chase mode
                    }
                }
                isScatter=0;
                isChase=1;
            }
            else if (chaseTimer<84){      //scatter4 for 5s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen
                        ghostArray[i]=2;   //scatter4
                    } 
                }
                isScatter=1;
                isChase=0;
            }
            else {
                for (i=0;i<4;i++){   //after scatter4, stay in chase
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
                isScatter=0;
                isChase=1;
            }
        }
        else if (isStart==1 && isFrightened == 1){ // if game is started and blinky is in frightened
            frightTimer++; //increment timer that keeps track of how long we've been in frighten mode
            int i;
            //sprintf(tft_str_buffer, "%d", frightTimer); //print new score
           // tft_printLine(4, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK, 2);  
            if (frightTimer>6) { //frighten mode lasts 6s
                for (i=0;i<4;i++){
                    //if (ghostArray[i]!=0){ //if ghosts not in pen, return them to previouse state
                        //DEAL WITH THIS LATER
                    ghostArray[i]=prevState[i];//remember to save prev state and change here, ie return to scatter or chase from frighten
                    //}
                    ghostColors[i]=ghostColorsInit[i];
                }
                
                isFrightened =0;
                frightTimer=0; //reset frighten timer 
                printf("end fright");
            }
        }
        
        //check if fruit have been printed and if yes, count to 10s
        if (isStart == 1 && fruitflag ==1){
            fruitCounter ++; 
            if (fruitCounter == 10){ //players have 10s to eat the fruit
                fruitflag = 0; //fruit has been Munched
                tft_fillCircle(120, 179, 3, ILI9340_BLACK); //remove the fruit
                dots[fruitxtile][fruitytile] = 0;
                fruitCounter = 0; //reset
            }
        }
    } // END WHILE(1)
    PT_END(pt);
} // timer thread

// === NEW LEVEL ===============================================================
void newlevel() {
    
    //reset counters
    numLevels++;
    dotsMunched = 0;
    numFruit = 0;  
    global_dotCounter =0;
    PdotCounter = 0;
    IdotCounter = 0;
    CdotCounter = 0; // maze is 244 dots
    
    //reset map and the kids
    resetMap();
    resetGhosts();
    if(numLevels == 3){
        level_256_bug();
    }
}

// === LEVEL 256 BUG FUNCTION ======================================================
/* in og game, screen is split due to an overflow error. The Hidden half of the map has totally different walls, tunnels, and only 9 dots, all of which are invisible to the player. No final victory because dots counter never reaches 244. 
 * our modifications: 
 * just clear the dots on the RHS
 * dont bother trying to figure out which of the 9 tiles in the OG still have dots
 * keep map and ghost logic unchanged, just invisible */
void level_256_bug(){
    bug256flag = 1; //set to high so animation thread only plots on LHS of screen 

    //clear dots on the rhs of screen 
    for(ii =0; ii < 36; ii++){ //28x36 tile grid, all rows
        for(jj = 14; jj < 28; jj++) //only columns on rhs
            dots[ii][jj] = 0;  //clear dots 
    }
    
    //map and ghosts have already been reset, need to plot over the RHS of the screen 
    //rectangles offset by 8x, 16y for plotting already. Fill rectangles and characters of color to match OG 
    
}// end 256 bug function

// === RESET MAP FUNCTION ======================================================
void resetMap() {
    //SIGH reset dots array
    for(ii =0; ii < 36; ii++){ //28x36 tile grid
        for(jj = 0; jj < 28; jj++)
            dots[ii][jj] = ogdots[ii][jj]; 
    }
    
    //then reset map
    tft_fillScreen(ILI9340_BLACK);
    int draw_row = 0;
    for(draw_row =0; draw_row < 36; draw_row++){ //28x36 tile grid
        int check_tile = 0;
        for(check_tile = 0; check_tile < 28; check_tile++){
            if(map[draw_row][check_tile] == 0){ //fill in legal space a different color from deadspace
                tft_fillRect((short) (8 + check_tile*8), (short) (16 + draw_row*8), (short) 8, (short) 8, ILI9340_BLUE);
            }
            if(dots[draw_row][check_tile] == 1) //draw small dots
                tft_drawPixel((short)(12 + check_tile*8), (short) (20 + draw_row*8), ILI9340_WHITE);
            else if(dots[draw_row][check_tile] == 2) //draw four Big Dots
                tft_fillCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 3, ILI9340_WHITE);
           }
    }
        
    //initialize score counter
    sprintf(tft_str_buffer,"Score"); 
    tft_printLine(1, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
    sprintf(tft_str_buffer,"%d", score); 
    tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
    
    //replot lives 
    //this thread is called in between levels so cant necessarily just replot all 3 lives
    tft_fillCircle(24,290,5,ILI9340_YELLOW); //plot the first life bc if lives < 1 game over
    if (lives >= 2) //if at least two lives left
        tft_fillCircle(35,290,5,ILI9340_YELLOW); //plot second life 
    if (lives == 3) // if all three lives left
        tft_fillCircle(46,290,5,ILI9340_YELLOW);  //plot third life

    if(isStart == 1) //only reset ghosts if game not over
        resetGhosts(); 
} // end map function

// === RESET GHOSTS FUNCTION ===================================================
void resetGhosts() {
    tft_fillCircle(xPacman,yPacman,3,ILI9340_BLACK); //remove pacman
    
    int z;
    for(z=0;z<4;z++){ //remove the ghosts and reset position to og location
        tft_fillCircle(xGhostPos[z],yGhostPos[z],2,ILI9340_BLACK); //plot over ghosts
        xGhostPos[z]=xGhostPosInit[z]; //put them back !!
        yGhostPos[z]=yGhostPosInit[z];
        prevGhostDir[z]=2;
        currGhostDir[z]=2;
        nextGhostDir[z]=2;
    }
    ghostArray[0] = 2; //put blinky in scatter mode
    int ii;
    for (ii=1;ii<4;ii++){ //set other ghost states to "in pen"
        ghostArray[ii]=0;
    }
    direction = 0; //not WASD so picman stops moving
    xPacman =120; 
    yPacman =228;
    
    //set ghost colors to black so that when a game ends and the animation thread finishes it replots all characters but u cant see them 
    if (lives == 0){
        int a;
        for (a=0;a<4;a++){
            ghostColors[a]=ILI9340_BLACK;
        }
        /*Blinky_Color = ILI9340_BLACK; 
        Pinky_Color = ILI9340_BLACK;
        Inky_Color = ILI9340_BLACK;
        Clyde_Color = ILI9340_BLACK;*/ //clyde <3
    }
    else {
        int a;
        for (a=0;a<4;a++){
            ghostColors[a]=ghostColorsInit[a];
        }
        /*Blinky_Color = ILI9340_RED; //reset ghosts to og colors
        Pinky_Color = ILI9340_PINK;
        Inky_Color = ILI9340_CYAN;
        Clyde_Color = ILI9340_ORANGE;*/ //c l y d e <333
    }
    isFrightened  = 0;
    isScatter=1;
    isChase=0;
    chaseTimer = 0; //reset timer for ghost behavior (scatter/chase timer)
    global_ghost_timer = 0;
    global_dotCounter = 0;
 } // end of resetGhosts function

// === CHECK DOTS FUNCTION =====================================================
// check if # dots Munched warrants a fruit or if the maze was cleared 
void checkDots() {
    //FRUIT ???
    if(dotsMunched >= 70 && numFruit == 0){ //check that 70 dots have been eaten and first fruit hasnt been printed yet
        //FRUIT!!
        fruitflag = 1; //set to high until Fruit Munched (tm)
        numFruit = 1; //
        tft_fillCircle(120, 179, 3, ILI9340_RED); //cherries? lol
        dots[fruitxtile][fruitytile] = 3; //set the dots array to a value thats not = small or big dot to keep track of when fruit is eaten
    }//end if dotsMunched >= 70
    
    else if(dotsMunched >= 170 && numFruit == 1){ //check that 170 dots have been eaten and second fruit hasnt been printed yet
        //fruit!!
        fruitflag = 1; //set to high until Fruit Munched (tm)
        numFruit = 2; //
        tft_fillCircle(120, 179, 3, ILI9340_RED); 
        dots[fruitxtile][fruitytile] = 3; //set the dots array to a value thats not = small or big dot to keep track of when fruit is eaten
    }//end if dotsMunched >= 170
    
    if (dotsMunched == 244){ //check if maze was cleared
        //characters pause and picman flashes
        ii = 0; //slow down flashing
        while (flashNum < 6) { //flashNum initialized to zero
            if(flashFlag == 0 && ii == 1000000){ // plot over picman to flash   
                tft_fillCircle(xPacman,yPacman,3,ILI9340_BLACK); //erase pic-man
                flashFlag = 1; //set flag to high for next time through the loop
                flashNum +=1;
                ii = 0;
            }
            else if(flashFlag == 1 && ii == 1000000){ // replot picman to flash
                tft_fillCircle(xPacman,yPacman,3,ILI9340_YELLOW); //erase pic-man
                flashFlag = 0; //set flag to 0 for next time through the loop
                flashNum +=1;
                ii = 0;
            } 
            ii++;
        } // end while
        flashNum = 0;
        newlevel();
    } //end if maze cleared
} // end check dots function

// === MOVE GHOSTS TO TARGET TILE FUNCTION =====================================
void moveGhosts(int ghost, int ghostX, int ghostY, int xTarget, int yTarget){
    //initialize variables
    int prevDir=prevGhostDir[ghost];
    int currDir=currGhostDir[ghost];
    int nextDir=nextGhostDir[ghost];
    int oppDir;
    int currXTile=(ghostX-8)/8;
    int currYTile=(ghostY-16)/8;
    int nextXPos, nextYPos;
    int nextXTile, nextYTile;
    int nextNextXTile, nextNextYTile;
    //check which direction we are moving and move 1 pixel in that direction
    if (currDir==1) { //up
        yGhostPos[ghost]-=1;
        if(prevDir==2 || prevDir==4){ //fix offset for turning
            xGhostPos[ghost]=currXTile*8+8+4;
        }
    }
    else if (currDir==2) { //left
        xGhostPos[ghost]-=1;
        if (xGhostPos[ghost]<12){ //wrap, this only happens at the "hallway"
            xGhostPos[ghost]=228;
        }
        if(prevDir==1 || prevDir==3){ //fix offset for turning
            yGhostPos[ghost]=currYTile*8+16+4;
        }
    }
    else if (currDir==3) { //down
        yGhostPos[ghost]+=1;
        if(prevDir==2 || prevDir==4){ //fix offset for turning
            xGhostPos[ghost]=currXTile*8+8+4;
        }
    }
    else if (currDir==4) { //right
        xGhostPos[ghost]+=1;
        if (xGhostPos[ghost]>228){ //wrap, this only happens at the "hallway"
            xGhostPos[ghost]=12;
        }
        if(prevDir==1 || prevDir==3){ //fix offset for turning
            yGhostPos[ghost]=currYTile*8+16+4;
        }
    }
    //calculate the tile we are in after moving 1 pixel
    nextXTile=(xGhostPos[ghost]-8)/8;
    nextYTile=(yGhostPos[ghost]-16)/8;
    //only calculate for the next next tile if we have entered a new tile
    if (nextXTile!=currXTile || nextYTile!=currYTile) {
        //calculate the next tile based off the direction we are about to move in
        nextXPos=xGhostPos[ghost];
        nextYPos=yGhostPos[ghost];
        if (nextDir==1) { //up
            nextYPos-=8; 
            oppDir=3;
        }
        else if (nextDir==2) { //left
            nextXPos-=8;
            if (nextXPos<8){
                nextXPos=231;
            }
            oppDir=4;
        }
        else if (nextDir==3) { //down
            nextYPos+=8;
            oppDir=1;
        }
        else if (nextDir==4) { //right
            nextXPos+=8;
            if (nextXPos>230){
                nextXPos=9;
            }
            oppDir=2;
        }
        
        prevGhostDir[ghost]=currDir; //save current direction as previous direction
        currGhostDir[ghost]=nextDir; //change current direction to predetermined next direction
        
        //Assess intended tile, check if tiles in the three potentially allowed directions are legal
        // only three potentially legal tiles bc we cannot reverse directions 
        int dirCounter;
        float shortestDist=1000; //arbitrary large number
        //loop through all directions
        for (dirCounter=1;dirCounter<=4;dirCounter++){
            short nextNextXPos=nextXPos;
            short nextNextYPos=nextYPos;
            //if this isn't the opposite direction, calculate next next x,y positions
            if (dirCounter!=oppDir){ 
                if (dirCounter==1){ //up
                    nextNextYPos-=8;
                }
                else if (dirCounter==2){ //left
                    nextNextXPos-=8;
                }
                else if (dirCounter==3){ //down
                    nextNextYPos+=8;
                }
                else if (dirCounter==4){ //right
                    nextNextXPos+=8;
                }
                nextNextXTile=(nextNextXPos-8)/8; //convert to tile
                nextNextYTile=(nextNextYPos-16)/8;
                if (map[nextNextYTile][nextNextXTile]==1){ //if the next tile is legal
                    short xDist=abs(xTarget-nextNextXPos);
                    short yDist=abs(yTarget-nextNextYPos);
                    float dist=max(xDist,yDist)+min(xDist,yDist)*.4;
                    if (dist<shortestDist){
                        shortestDist=dist;
                        nextGhostDir[ghost]=dirCounter;
                    } //end if shortest distance
                } //end if tile is legal
            } //end if not the opposite direction
        } //end for all directions loop
    } //end if we are in new tile
} // end moveGhosts

// === MOVE GHOSTS DURING FRIGHTEN MODE ========================================
void moveGhostsFrightenMode(int ghost, int ghostX, int ghostY) {
    //initialize variables
    
    int nextDir=nextGhostDir[ghost];
    int oppDir;
    int currXTile=(ghostX-8)/8;
    int currYTile=(ghostY-16)/8;
    int nextXPos, nextYPos;
    int nextXTile, nextYTile;
    int nextNextXTile, nextNextYTile;
    
    /*CONCEPT: - ONLY ON FIRST RUN
     1. find prev dir, based upon reversing
     2. determine the last tile u were in based upon ur prev direction
     3. calculate ur next next tile based upon the previous tile you were in
     4. find the allowable directions on your next next tile
     5. pick a random number and go in that direction
     */
    
    //step 1: reverse direction when we enter frighten mode, set prevDir
    if(frightStart[ghost] == 1){
        if(currGhostDir[ghost] == 1){
            currGhostDir[ghost] = 3;
            //nextGhostDir[ghost] = 3;
        }
        else if(currGhostDir[ghost] == 2){
            currGhostDir[ghost] = 4;
            //nextGhostDir[ghost] = 4;
        }
        else if(currGhostDir[ghost] == 3){
            currGhostDir[ghost] = 1;
            //nextGhostDir[ghost] = 1;
        }
        else{
            currGhostDir[ghost] = 2;
            //nextGhostDir[ghost] = 2;
        }
    }  
    
    int prevDir=prevGhostDir[ghost];
    int currDir=currGhostDir[ghost];
   
    //check which direction we are moving and move 1 pixel in that direction
    if (currDir==1) { //up
        yGhostPos[ghost]-=1;
    }
    else if (currDir==2) { //left
        xGhostPos[ghost]-=1;
        if (xGhostPos[ghost]<12){ //wrap, this only happens at the "hallway"
            xGhostPos[ghost]=228;
        }
    }
    else if (currDir==3) { //down
        yGhostPos[ghost]+=1;
    }
    else if (currDir==4) { //right
        xGhostPos[ghost]+=1;
        if (xGhostPos[ghost]>228){ //wrap, this only happens at the "hallway"
            xGhostPos[ghost]=12;
        }
    }
   
    nextXTile=(xGhostPos[ghost]-8)/8;
    nextYTile=(yGhostPos[ghost]-16)/8;
    
    
    //calculate the tile we are in after moving 1 pixel
    //nextXTile=(xGhostPos[ghost]-8)/8;
    //nextYTile=(yGhostPos[ghost]-16)/8;
    //only calculate for the next next tile if we have entered a new tile
    if (nextXTile!=currXTile || nextYTile!=currYTile || frightStart[ghost] == 1) {
        //calculate the next tile based off the direction we are about to move in
        nextXPos=xGhostPos[ghost];
        nextYPos=yGhostPos[ghost];
        
        if(frightStart[ghost] ==1){
            nextXPos=ghostX;
            nextYPos=ghostY;
        
            nextDir = currDir;
        }
        
        
       
        if (nextDir==1) { //up
            nextYPos-=8; 
            oppDir=3;
        }
        else if (nextDir==2) { //left
            nextXPos-=8;
            if (nextXPos<8){
                nextXPos=231;
            }
            oppDir=4;
        }
        else if (nextDir==3) { //down
            nextYPos+=8;
            oppDir=1;
        }
        else if (nextDir==4) { //right
            nextXPos+=8;
            if (nextXPos>230){
                nextXPos=9;
            }
            oppDir=2;
        }
        
        prevGhostDir[ghost]=currDir; //save current direction as previous direction
        currGhostDir[ghost]=nextDir; //change current direction to predetermined next direction
        
        //Assess intended tile, check if tiles in the three potentially allowed directions are legal
        // only three potentially legal tiles bc we cannot reverse directions 
        int dirCounter =1;
        int index = 0;
        int validDirs[4] = {0,0,0,0}; 
        //loop through all directions
        for (dirCounter=1;dirCounter<=4;dirCounter++){
            short nextNextXPos=nextXPos;
            short nextNextYPos=nextYPos;
            //if this isn't the opposite direction, calculate next next x,y positions
            if (dirCounter!=oppDir){ 
                if (dirCounter==1){ //up
                    nextNextYPos-=8;
                }
                else if (dirCounter==2){ //left
                    nextNextXPos-=8;
                }
                else if (dirCounter==3){ //down
                    nextNextYPos+=8;
                }
                else if (dirCounter==4){ //right
                    nextNextXPos+=8;
                }
                nextNextXTile=(nextNextXPos-8)/8; //convert to tile
                nextNextYTile=(nextNextYPos-16)/8;
                if (map[nextNextYTile][nextNextXTile]==1){ //if the next tile is legal 
                    validDirs[index] = 1;
                }//if legal tile
                index++;
            }//end if not opp dir
        }//end for loop   
        
        //printf("valid dirs[1] %d\n", validDirs[0]);
        //printf("valid dirs[2] %d\n", validDirs[1]);
        //printf("valid dirs[3] %d\n", validDirs[2]);
        //printf("valid dirs[4] %d\n", validDirs[3]);
        
        int rand_numb = (rand() % 2) + 1;
        //printf("rand numb  = %d\n", rand_numb);
        int map_counter = 0;
        int rr =0;;
        nextDir = 0;
        while(nextDir==0){
            //printf("in while");
            if (validDirs[rr] != 0){
                map_counter++;
                if (map_counter == rand_numb) {
                    //prevGhostDir[ghost]=currDir; //save current direction as previous direction
                    //currGhostDir[ghost]=nextDir; //change current direction to predetermined next direction
                    nextDir = rr + 1;
                }//end if map counter
            }//end if valid dir
            rr++;
            if(rr == 3){
                rr =0;
            }
        } //end while loop
        nextGhostDir[ghost] = nextDir;
   }//end if not current tile
   if(frightStart[ghost] ==1){
       frightStart[ghost] =0;
   }
 //}//end if first time
    
  
}//end function


// === ANIMATION THREAD==================================================== //
// plots picman continuously in direction last set by GUI input
// if ghosts in frighten mode, choose direction at intersection randomly
// if ghosts in scatter mode, path logic according to home tile
// if ghosts in chase mode, path logic according to target tile = f(picman's current tile)
                        
static PT_THREAD (protothread_animation (struct pt *pt)){
    PT_BEGIN(pt);
    while(1){
        begin_time = PT_GET_TIME();  // objective animation speed 60FPS
        
        ////////////PAC MAN /////////////////////////////////
        static int currentxPacman;
        static int currentyPacman;
        static int current_xtile;
        static int current_ytile;
        
        currentxPacman = xPacman;
        currentyPacman = yPacman;
        current_xtile = (xPacman-8)/8; //we centered the maze on the TFT. subtract centering offset and divide by 8 to get tile
        current_ytile = (yPacman - 16)/8; 
        
        if (isStart==1){ //only animate if game has started
            //----- MUNCH THE DOTS ---------------------------------------------
            if(dots[current_ytile][current_xtile]==1){ //if pacman passes through a new dot
                score+=10; //then increase points
                dotsMunched++;    //increase the dots counter that keeps track of when the maze is reset/level complete
                global_ghost_timer = 0; //rest ghost timer if dot is eaten
                checkDots(); // check for fruit of if the maze was cleared 
                
                //move ghosts out of pen based on dots eaten
                if(lives == 3){ //if 1 life lost, switch to global dot counter
                    if(PdotCounter < 1){ //dot counter limits for each ghost - blinkys is zero
                        PdotCounter++;
                    }
                    else if(IdotCounter < 31){
                        IdotCounter++;
                    }
                    else if(CdotCounter < 61){
                        CdotCounter++;
                    }
                }
                else{
                    global_dotCounter++;
                }
                
                dots[current_ytile][current_xtile]=0; //note that the dot is gone by updating array
                sprintf(tft_str_buffer,"%d", score); //print new score
                tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);        
            } // end if current tile contains a small dot
            
            else if (dots[current_ytile][current_xtile]==2){ //if current tile contains a big dot
                score+=50; // increase points 
                dotsMunched++; //increase dots counter. max 244
                isFrightened = 1;
                
                //isScatter = 0;
                //isChase = 0;
                checkDots(); // check if fruit or if maze cleared  
                
                dots[current_ytile][current_xtile]=0; //store new dot value
                int i;
                for (i=0;i<4;i++){ //trigger frighten mode
                    if(ghostArray[i] != 0){
                        prevState[i]=ghostArray[i]; //store previous mode for when frightened is over
                        ghostArray[i]=3; //doin me a frighten
                        frightStart[i] = 1;
                    }
                    ghostColors[i]=ILI9340_BLUE;
                }
                //printf("isFrightened value  = %d \n", isFrightened);
                //tft_fillCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 4, ILI9340_WHITE);
                tft_fillCircle((short)(12+current_xtile*8),(short)(20+current_ytile*8),3,ILI9340_BLACK);  //erase Big Dot
                sprintf(tft_str_buffer,"%d", score); //print new score
                tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2); 
            } // end if current tile contains big dot
            
            else if (dots[current_ytile][current_xtile]==3){ //if current tile contains a fruit
                score+=100; // cherries for level1 worth 100pts 
                fruitflag = 0; //fruit has been Munched
                tft_fillCircle(120, 179, 3, ILI9340_BLACK); //remove the fruit
                dots[fruitxtile][fruitytile] = 0;
            }

            // ------ PLOT MsPICMAN ------------------------------------------
            //basically, picman moves according to last direction set by gui
            // we have the current tile, we increment pixel position, then calculate "new_tile"
            // if new tile is dead, then decrement the pixel position and this process repeats (picman stops moving @walls)
            //if legal tile, proceed w plotting 
            int new_xtile; 
            int new_ytile;
            /*move in direction*/
            if ((direction==1) && (collisionFlag != 1)) { //up, don't update position if in lost life sequence
                yPacman-=1; //positive y is defined down for tft 
                new_xtile = (xPacman-8)/8; //this is the tile she wants to move to but we need to check if its legal first
                new_ytile = ((yPacman-4) - 16)/8;
                if (map[new_ytile][new_xtile]==0){ //if new tile is dead space
                    yPacman+=1; //then decrement position back
                    if (prevDirection!=0) //if the user tried to move up but it turned out to be illegal
                        direction=prevDirection; //reset the previous direction
                }
                else { // tile is legal
                    if (prevDirection==2 || prevDirection==4){//check if turned from left/right
                        xPacman=current_xtile*8+8+4; //calculate new xtile
                    }
                    prevDirection=direction; //set previous direction now because direction is updaed when GUI is changed
                }
            }    
            else if ((direction==2) && (collisionFlag != 1)) { //left
                xPacman-=1;
                if (xPacman<10) //wrap, this only happens at the "hallway"
                    xPacman=228;
                new_xtile = ((xPacman-4)-8)/8;
                new_ytile = (yPacman - 16)/8;
                if (map[new_ytile][new_xtile]==0) {//if dead
                    if(xPacman==228) 
                        xPacman=10;
                    else
                        xPacman+=1;
                    if (prevDirection!=0)
                        direction=prevDirection;
                }
                else {
                    if (prevDirection==1 || prevDirection==3){//check if turned from left/right
                        yPacman=current_ytile*8+16+4;
                    }
                    prevDirection=direction;
                }
            }
            else if ((direction==3)&&(collisionFlag != 1)) { //down
                yPacman+=1;
                new_xtile = (xPacman-8)/8;
                new_ytile = ((yPacman+4) - 16)/8;
                if (map[new_ytile][new_xtile]==0) {
                    yPacman-=1;
                    if (prevDirection!=0)
                        direction=prevDirection;
                }
                else {
                    if (prevDirection==2 || prevDirection==4){//check if turned from left/right
                        xPacman=current_xtile*8+8+4;
                    }
                    prevDirection=direction;
                }
            }
            else if ((direction==4) && (collisionFlag != 1)) { //right
                xPacman+=1;
                if (xPacman>227) //wrap
                    xPacman=10; 
                new_xtile = ((xPacman+4)-8)/8;
                new_ytile = (yPacman - 16)/8;
                if (map[new_ytile][new_xtile]==0) {
                    if(xPacman==10)
                        xPacman=227;
                    else
                        xPacman-=1;
                    if (prevDirection!=0)
                        direction=prevDirection;
                }
                else {
                    if (prevDirection==1 || prevDirection==3){//check if turned from left/right
                        yPacman=current_ytile*8+16+4;
                    }
                    prevDirection=direction;
                }
            }//end pac-man arrow key logic
            
            //////////////// GHOSTS ////////////////////////////
            //save current positions and tiles before update
            int aa;
            for(aa=0;aa<4;aa++){
                currXGhostPos[aa]=xGhostPos[aa];
                currYGhostPos[aa]=yGhostPos[aa];
                currXGhostTile[aa]=(currXGhostPos[aa]-8)/8;
                currYGhostTile[aa]=(currYGhostPos[aa]-16)/8; 
            }
            ///////PINY///////
            if((PdotCounter == 1 || (lives < 3 && global_dotCounter == 7) 
                    || (global_ghost_timer >= 4)) && ghostArray[1] == 0){

                xGhostPos[1] = 120; //move pinky above pen when counter limit is reached
                yGhostPos[1] = 132; 

                PdotCounter = 2;
                global_ghost_timer = 0;
                ghostArray[1] = ghostArray[0];
            }
            ///////INKY///////
            if((IdotCounter == 31 || (lives < 3 && global_dotCounter == 17)
                    || (global_ghost_timer >= 4)) && ghostArray[2] == 0){
                xGhostPos[2] = 120; //move pinky above pen when counter limit is reached
                yGhostPos[2] = 132; 

                //current_xItile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
                //current_yItile = (yPinky - 16)/8;
                IdotCounter = 32;
                global_ghost_timer = 0;
                ghostArray[2] = ghostArray[0];
            }
            ////////CLYDE/////// <3 
            if((CdotCounter == 61 || (lives < 3 && global_dotCounter == 32)
                    || (global_ghost_timer >= 4)) && ghostArray[3] == 0){
                xGhostPos[3] = 120; //move pinky above pen when counter limit is reached
                yGhostPos[3] = 132; 

                //current_xCtile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
                //current_yCtile = (yPinky - 16)/8;
                CdotCounter = 62;
                global_ghost_timer = 0;
                ghostArray[3] = ghostArray[0];
            } 
            
            //ghost modes
            if (isChase==1){ //if in chase mode 
                //blinky target tile
                //printf("in chase");
                xTarget[0]=currentxPacman;
                yTarget[0]=currentyPacman;
                if (direction==1 && collisionFlag!=1){ //up
                    //pinky target tile
                    xTarget[1]=currentxPacman-32; //4 tiles
                    yTarget[1]=currentyPacman-32;
                    //inky target tile
                    int halfwayXTile=((currentxPacman-16)-8)/8;
                    int halfwayYTile=((currentyPacman-16)-16)/8;
                    xTarget[2]=halfwayXTile+(halfwayXTile-currXGhostTile[0]);
                    yTarget[2]=halfwayYTile+(halfwayYTile-currYGhostTile[0]);
                }
                else if (direction==1 && collisionFlag!=1){ //left
                    //pinky target tile
                    xTarget[1]=xPacman-32; //4 tiles
                    yTarget[1]=yPacman;
                    //inky target tile
                    int halfwayXTile=((currentxPacman-16)-8)/8;
                    int halfwayYTile=((currentyPacman)-16)/8;
                    xTarget[2]=halfwayXTile+(halfwayXTile-currXGhostTile[0]);
                    yTarget[2]=halfwayYTile+(halfwayYTile-currYGhostTile[0]);
                }
                else if (direction==1 && collisionFlag!=1){ //down
                    //pinky target tile
                    xTarget[1]=xPacman; //4 tiles
                    yTarget[1]=yPacman+32;
                    //inky target tile
                    int halfwayXTile=((currentxPacman)-8)/8;
                    int halfwayYTile=((currentyPacman)+16)/8;
                    xTarget[2]=halfwayXTile+(halfwayXTile-currXGhostTile[0]);
                    yTarget[2]=halfwayYTile+(halfwayYTile-currYGhostTile[0]);
                }
                else if (direction==1 && collisionFlag!=1){ //right
                    //pinky target tile
                    xTarget[1]=xPacman+32; //4 tiles
                    yTarget[1]=yPacman;
                    //inky target tile
                    int halfwayXTile=((currentxPacman+16)-8)/8;
                    int halfwayYTile=((currentyPacman))/8;
                    xTarget[2]=halfwayXTile+(halfwayXTile-currXGhostTile[0]);
                    yTarget[2]=halfwayYTile+(halfwayYTile-currYGhostTile[0]);
                }
                else{ //pacman isn't moving so arrow input isnt 1,2,3 or 4 (left)
                    xTarget[1]=xPacman-32; //4 tiles
                    yTarget[1]=yPacman;
                    //inky target tile
                    int halfwayXTile=((currentxPacman-16)-8)/8;
                    int halfwayYTile=((currentyPacman))/8;
                    xTarget[2]=halfwayXTile+(halfwayXTile-currXGhostTile[0]);
                    yTarget[2]=halfwayYTile+(halfwayYTile-currYGhostTile[0]);
                }
                //clyde <3 target tile 
                short xDist=abs(currXGhostTile[3]-currentxPacman);
                short yDist=abs(currYGhostTile[3]-currentyPacman);
                float dist=max(xDist,yDist)+min(xDist,yDist)*.4;
                if (dist>64){
                    xTarget[3]=currentxPacman;
                    yTarget[3]=currentyPacman;
                }
                else{
                    xTarget[3]=8;
                    yTarget[3]=296;
                }
                int ii;
                for(ii=0;ii<4;ii++) { //loop through ghosts //CHANGE FROM 2 - 1 for testing
                    if (ghostArray[ii]!=3 && ghostArray[ii]!=0){
                        moveGhosts(ii, xGhostPos[ii], yGhostPos[ii], xTarget[ii], yTarget[ii]);
                    }
                } 
            }
            else if (isScatter==1){
                //printf("in scatter");
                xTarget[0]=208;//tile (25,0)
                yTarget[0]=16;
                xTarget[1]=24;//tile (2,0)
                yTarget[1]=16;
                xTarget[2]=224;//tile (27,35)
                yTarget[2]=296;
                xTarget[3]=8;//tile (0,35)
                yTarget[3]=296;
                int ii;
                for(ii=0;ii<4;ii++) {
                    //loop through ghosts //CHANGE FROM 2 - 1 for testing
                    if (ghostArray[ii]!=3 && ghostArray[ii]!=0){
                        moveGhosts(ii, xGhostPos[ii], yGhostPos[ii], xTarget[ii], yTarget[ii]);
                    }
                }
            }
            
            if(isFrightened == 1){
                
                int ii;
                for(ii=0;ii<1;ii++) { //loop through ghosts //CHANGE FROM 2 - 1 for testing
                    if (ghostArray[ii]==3 && ghostArray[ii]!=0){
                        //printf("in fright if\n");
                        moveGhostsFrightenMode(ii, xGhostPos[ii], yGhostPos[ii]);
                    }
                }
            }
            
            ////////// CHECK FOR COLLISIONS ////////////////////////////////
            // do this after tiles have been updated for all characters
            // could use for OR operators and do this all at once but realllllly long if condition 
            int bb;
            for(bb=0;bb<4;bb++) {
                if (current_xtile==currXGhostTile[bb] && current_ytile==currYGhostTile[bb]){
                    if(ghostArray[bb] != 3){ //if not in frighten mode
                        lives -= 1; //lose a life rip
                        // all characters pause and picman dies
                        collisionFlag = 1;
                    }
                    else{ 
                        ghostColors[bb] = ghostColorsInit[bb]; //when frighten mode triggered, blinky is set to blue. replot in red once Munched(tm)
                        xGhostPos[bb] = 120; // plot blinky in OG position
                        yGhostPos[bb] = 132;
                        prevGhostDir[bb]=2;
                        currGhostDir[bb]=2;
                        nextGhostDir[bb]=2;
                        ghostsEaten++;
                        score += 200 * ghostsEaten;
                        ghostArray[bb] = prevState[bb]; // put him back in whatever mode he was in before being Frightened 
                    }
                }
            }
            
            // IF collision AND not in frighten mode
            // all characters pause, picman dies (flashing)
            // picman doesnt move until gui input again 
            // ghosts are reset, timer for ghost modes is reset 
            if (collisionFlag == 1){   //if collision occurs, animate death and replot   
            // in game, ms pacman kinda warps into nothing but we dont have that resolution so im just going to have her flash        
                printf("in collision if /n");
                while (flashNum < 8) { //flashNum initialized to zero
                    PT_YIELD_TIME_msec(300); //this is here to slow down the death animation
                    if(flashFlag == 0){ // plot over picman to flash
                     sprintf(tft_str_buffer,"%d",currentxPacman); //print success
                     tft_printLine(15, 2, tft_str_buffer, ILI9340_BLUE, ILI9340_BLACK,4);    
                        tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); //erase pic-man
                        flashFlag = 1; //set flag to high for next time through the loop
                        flashNum +=1;
                    }
                    else if(flashFlag == 1){ // replot picman to flash
                        tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_YELLOW); //erase pic-man
                        flashFlag = 0; //set flag to 0 for next time through the loop
                        flashNum +=1;
                    } 
                } // end while
                
                //done flashing, replot characters and unpause 
                //replotting is done at the end of this thread, so here we just reset the coordinates to be plotted
                direction = 5; //some number that's not wasd so picman stops moving 
                xPacman=120;   //initial pacman position 
                yPacman=228;
                resetGhosts();

                //update lives display
                if(lives == 2){
                tft_fillCircle(46,290,5,ILI9340_BLUE); //draw over life
                }
                if(lives == 1){
                    tft_fillCircle(35,290,5,ILI9340_BLUE); //draw over life
                }
                if(lives == 0){ //game over loser
                    tft_fillCircle(24,290,5,ILI9340_BLUE); //draw over life
                    tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); //erase pic-man
                    
                   //PRINT GAME OVER
                   sprintf(tft_str_buffer, " GAME OVER");  //sucks2suck
                   tft_printLine(3, 0, tft_str_buffer, ILI9340_BLUE, ILI9340_BLACK,4);    
                   PT_YIELD_TIME_msec(1000); 
                   
                   //set a flag to trigger game over sequence
                   //possibly move all of the variable resets somewhere else ? 
                   //might make sense to put them in the button thread but like "if isStart !=1 already" so game doesnt break
                   gameOverFlag = 1;
                   isStart = 0; //but we still finish this time through the loop so ghosts r animated one last time 
                   lives = 3;   //update now for when the map is reset in 2s
                   score = 0;
                   //dots = 0;
                   global_dotCounter = 0;
                   PdotCounter = 0;
                   IdotCounter = 0;
                   CdotCounter = 0; // maze is 244 dots
                   resetMap();
                   
                }//end if lives = 0
         
                flashNum = 0; //reset to zero for next collision
                collisionFlag = 0; //let characters animate again
            }//end if collisionFlag == 1
            
            // START COPY N PASTE HERE
            if (bug256flag == 1){ // if we're on the level that replicates the 256 bug
                //erase all characters
                tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); 
                int cc;
                for(cc=0;cc<4;cc++){
                    tft_fillCircle(currXGhostPos[cc],currYGhostPos[cc],2,ILI9340_BLACK); //erase ghost
                }

                //but only replot them if on LHS of screen 
                if(xPacman < 120){
                    tft_fillCircle(xPacman,yPacman,3,ILI9340_YELLOW); //plot new picman
                }
                for(cc=0;cc<4;cc++){
                    if(currXGhostPos[cc] < 120){
                        if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==1){
                            tft_drawPixel((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8), ILI9340_WHITE);
                        }
                        else if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==2){
                            tft_fillCircle((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8),(short) 3, ILI9340_WHITE);
                        }
                        tft_fillCircle(xGhostPos[cc],yGhostPos[cc],2,ghostColors[cc]); //plot new ghost
                    }
                }

            }
            else{
                tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); //erase pic-man
                tft_fillCircle(xPacman,yPacman,3,ILI9340_YELLOW); //plot new picman
                
                int cc;
                for(cc=0;cc<4;cc++){
                    tft_fillCircle(currXGhostPos[cc],currYGhostPos[cc],2,ILI9340_BLACK); //erase ghost
                    
                    if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==1){
                        tft_drawPixel((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8), ILI9340_WHITE);
                    }
                    else if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==2){
                        tft_fillCircle((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8),(short) 3, ILI9340_WHITE);
                    }
                    tft_fillCircle(xGhostPos[cc],yGhostPos[cc],2,ghostColors[cc]); //plot new ghost
                }
            }
            // END COPY N PASTE HERE
           
            
            /* GRACES ANIMATION CODE
            tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); //erase pic-man
            tft_fillCircle(xPacman,yPacman,3,ILI9340_YELLOW); //plot new picman
            
            int cc;
            for(cc=0;cc<4;cc++){
                tft_fillCircle(currXGhostPos[cc],currYGhostPos[cc],2,ILI9340_BLACK); //erase ghost
                
                if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==1){
                    tft_drawPixel((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8), ILI9340_WHITE);
                }
                else if (dots[currYGhostTile[cc]][currXGhostTile[cc]]==2){
                    tft_fillCircle((short)(12 + currXGhostTile[cc]*8), (short) (20 + currYGhostTile[cc]*8),(short) 3, ILI9340_WHITE);
                }
                tft_fillCircle(xGhostPos[cc],yGhostPos[cc],2,ghostColors[cc]); //plot new ghost
            }*/
            
            //this is such a jank solution i hate it 
            if (gameOverFlag == 1){
                //reset flag next time the game is started 
                tft_fillCircle(xPacman,yPacman,3,ILI9340_BLACK); //plot new picman
            }
        } //end of if isStart 
        
        // 30 fps => frame time of 32 mSec. This blurb checks that we're meeting that goal
        check_time = PT_GET_TIME() - begin_time; //checks if more than 32 msec has passed
        if(check_time > 32){
            mPORTAClearBits(BIT_0); // turn off LED if below 30FPS
            //printf("rip");
        }
        else{
            mPORTASetBits(BIT_0); // turn LED on IF we meet 30FPS 
        }
        
        PT_YIELD_TIME_msec(32 - check_time);   
    } // end while(1)) before PT_END st it's never executed
    PT_END(pt);
} //close thread

// === outputs from python handler =============================================
// signals from the python handler thread to other threads
// These will be used with the protothreads PT_YIELD_UNTIL(pt, condition);
// to act as semaphores to the processing threads
char new_string = 0;
char new_button = 0;
char new_arrow = 0;

// identifiers and values of controls
// current button
char button_id, button_value ;
//current arrow/direction
char arrow_id,arrow_value; //1,2,3,4 for up left down R

// current string
char receive_string[64];

// === string input thread =====================================================
// process text from python
static PT_THREAD (protothread_python_string(struct pt *pt))
{
    PT_BEGIN(pt);
    while(1){
        // wait for a new string from Python
        PT_YIELD_UNTIL(pt, new_string==1);
        //clear string flag
        new_string = 0;
        tft_printLine(1,0, receive_string, ILI9340_GREEN, ILI9340_BLACK, 2);
        printf("received>%s", receive_string);        
    } // END WHILE(1)   
    PT_END(pt);  
} // thread python_string


// === Arrows thread ===========================================================
// parses arrow_id to set whether new direction is UP DOWN LEFT or RIGHT
//1,2,3,4 for up left down 
static PT_THREAD (protothread_arrows(struct pt *pt))
{
    PT_BEGIN(pt);
    while(1){
        PT_YIELD_UNTIL(pt, new_arrow==1);
        seed_counter++;
        // clear flag
        new_arrow = 0;  
        if (arrow_value==1){
            direction = arrow_id;
            srand(seed_counter);
            //printf("%d",direction);
        }
        //tft_fillCircle(280,200,5,ILI9340_MAGENTA);
        //sprintf(tft_str_buffer,"%d", direction); 
        //tft_printLine(4, 5, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,5);
        
        //1,2,3,4 for up left down R
        
    } // END WHILE(1)   
    PT_END(pt);  
} // arrow thread

// === Buttons thread ==========================================================
// Notes when to start the game based on when the user presses the start button in GUI
static PT_THREAD (protothread_buttons(struct pt *pt))
{
    PT_BEGIN(pt);
    while(1){
        PT_YIELD_UNTIL(pt, new_button==1);
        // clear flag
        new_button = 0;   
        if (button_id==1 && button_value==1){
            // change some var to true to signal game start
            //tft_fillScreen(ILI9340_RED); //debug
            if (gameOverFlag == 1){
                resetGhosts();
                gameOverFlag = 0; 
                // reset here so that I can use it to check if the game was previously played since pic reset
                // if new game without pic reset, need to reset ghosts so their colors are normal
            }
            isStart=1;
        }
    } // END WHILE(1)   
    PT_END(pt);  
} // thread buttons

// === Python serial thread ====================================================
// you should not need to change this thread UNLESS you add new control types
static PT_THREAD (protothread_serial(struct pt *pt))
{
    PT_BEGIN(pt);
    static char junk;
    //   
    //
    while(1){
        // There is no YIELD in this loop because there are
        // YIELDS in the spawned threads that determine the 
        // execution rate while WAITING for machine input
        // =============================================
        // NOTE!! -- to use serial spawned functions
        // you MUST edit config_1_3_2 to
        // (1) uncomment the line -- #define use_uart_serial
        // (2) SET the baud rate to match the PC terminal
        // =============================================
        
        // now wait for machine input from python
        // Terminate on the usual <enter key>
        PT_terminate_char = '\r' ; 
        PT_terminate_count = 0 ; 
        PT_terminate_time = 0 ;
        // note that there will NO visual feedback using the following function
        PT_SPAWN(pt, &pt_input, PT_GetMachineBuffer(&pt_input) );
        
        // Parse the string from Python
        // There can be toggle switch, button, slider, and string events
        // Updated to add WASD and arrow key control input to change PICMAN direction 
        //1,2,3,4 for up left down R
        //printf("%s\n",PT_term_buffer);
        if (PT_term_buffer[0]=='a'){
            // signal the button thread
            new_arrow = 1;
            // subtracting '0' converts ascii to binary for 1 character
            arrow_id = (PT_term_buffer[1] - '0')*10 + (PT_term_buffer[2] - '0');
            arrow_value=PT_term_buffer[4]-'0';
            //printf("%s\n",PT_term_buffer);
        }
      
        // pushbutton
        if (PT_term_buffer[0]=='b'){
            // signal the button thread
            new_button = 1;
            // subtracting '0' converts ascii to binary for 1 character
            button_id = (PT_term_buffer[1] - '0')*10 + (PT_term_buffer[2] - '0');
            button_value = PT_term_buffer[3] - '0';
            //printf("%s\n",PT_term_buffer);
        }
        
        // string from python input line
        if (PT_term_buffer[0]=='$'){
            // signal parsing thread
            new_string = 1;
            // output to thread which parses the string
            // while striping off the '$'
            strcpy(receive_string, PT_term_buffer+1);
        }
                                          
    } // END WHILE(1)   
    PT_END(pt);  
} // thread blink

// === Main  ======================================================

void main(void) {
    // === configure LED check for animation rate
    mPORTASetPinsDigitalOut(BIT_0);    //Set port as output
    mPORTASetBits(BIT_0); // initialize LED on, turn off if we don't meet 30FPS
    
  //// 32 BIT interrupt //////////////////////////
    // Set up timer23 on,  interrupts, internal clock, prescalar 1, toggle rate
    //ie chain timers 2 and 3 together to create a 32 bit timer
    OpenTimer23(T2_ON | T2_SOURCE_INT | T2_PS_1_1 | T2_32BIT_MODE_ON, TIMEOUT);

    // set up the timer interrupt with a priority of 2
    ConfigIntTimer23(T23_INT_ON | T23_INT_PRIOR_2);
    mT3ClearIntFlag(); // and clear the interrupt flag
    
 ///// 16 Bit timer interrupt /////////////////////////////////////  
    OpenTimer4(T4_ON | T4_SOURCE_INT | T4_PS_1_1 , TIMEOUT4);
    
    ConfigIntTimer4(T4_INT_ON | T4_INT_PRIOR_2);
    mT4ClearIntFlag(); // and clear the interrupt flag
    
 ///// 16 bit transfer CKP=1 CKE=1 ////////////////////////////////////////////
    // possibles SPI_OPEN_CKP_HIGH;   SPI_OPEN_SMP_END;  SPI_OPEN_CKE_REV
    // For any given peripherial, you will need to match these
    SpiChnOpen(SPI_CHANNEL2, SPI_OPEN_ON | SPI_OPEN_MODE16 | SPI_OPEN_MSTEN | SPI_OPEN_CKE_REV , 2);
    
//// the DAC ///////////////////////////////////////
    // configure and enable the DAC in case we get to PICMAN sounds

    // === DAC sin table =========================
   
    
  //// === setup system wide interrupts  ========
  INTEnableSystemMultiVectoredInt();
  
  // === TFT setup ============================
  // init the display in main since more than one thread uses it.
  // NOTE that this init assumes SPI channel 1 connections
  tft_init_hw();
  tft_begin();
  tft_fillScreen(ILI9340_BLACK);
  //240x320 vertical display
  tft_setRotation(0); // Use tft_setRotation(1) for 320x240
  
    /*draw map*/
    int draw_row = 0;
    for(draw_row =0; draw_row < 36; draw_row++){ //28x36 tile grid
        int check_tile = 0;
        for(check_tile = 0; check_tile < 28; check_tile++){
            if(map[draw_row][check_tile] == 0){ //fill in legal space a different color from deadspace
                tft_fillRect((short) (8 + check_tile*8), (short) (16 + draw_row*8), (short) 8, (short) 8, ILI9340_BLUE);
            }
            if(dots[draw_row][check_tile] == 1) //draw small dots
                tft_drawPixel((short)(12 + check_tile*8), (short) (20 + draw_row*8), ILI9340_WHITE);
            else if(dots[draw_row][check_tile] == 2) //draw four Big Dots
                tft_fillCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 3, ILI9340_WHITE);
        }
    }
    
    
    
    //initialize score counter
    sprintf(tft_str_buffer,"Score"); 
    tft_printLine(1, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
    sprintf(tft_str_buffer,"%d", score); 
    tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
    
    //initialize lives 
    tft_fillCircle(24,290,5,ILI9340_YELLOW); //whenlives are lost, plot over them from R to L
    tft_drawCircle(24,290,5,ILI9340_BLACK); //does nothing visually rip
    tft_fillCircle(35,290,5,ILI9340_YELLOW); 
    tft_drawCircle(35,290,5,ILI9340_BLACK); 
    tft_fillCircle(46,290,5,ILI9340_YELLOW); 
    tft_drawCircle(46,290,5,ILI9340_BLACK); 
  
  
  // === config threads ========================
  PT_setup();
  
  // === identify the threads to the scheduler =====
  // add the thread function pointers to be scheduled
  // --- Two parameters: function_name and rate. ---
  // rate=0 fastest, rate=1 half, rate=2 quarter, rate=3 eighth, rate=4 sixteenth,
  // rate=5 or greater DISABLE thread!
   
  pt_add(protothread_buttons, 0);
  pt_add(protothread_timer, 0);
  pt_add(protothread_serial, 0);
  pt_add(protothread_python_string, 0);
  pt_add(protothread_arrows, 0);
  pt_add(protothread_animation, 0);

  
  // === initalize the scheduler ====================
  PT_INIT(&pt_sched) ;
  // >>> CHOOSE the scheduler method: <<<
  // (1)
  // SCHED_ROUND_ROBIN just cycles thru all defined threads
  //pt_sched_method = SCHED_ROUND_ROBIN ;
  
  // NOTE the controller must run in SCHED_ROUND_ROBIN mode
  // ALSO note that the scheduler is modified to cpy a char
  // from uart1 to uart2 for the controller
  
  pt_sched_method = SCHED_ROUND_ROBIN ;
  
  // === scheduler thread =======================
  // scheduler never exits
  PT_SCHEDULE(protothread_sched(&pt_sched));
  // ============================================
  
} // main
// === end  ======================================================

