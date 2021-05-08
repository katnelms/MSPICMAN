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

//test comment for grace :)
//test comment for grace part 2 :)
//test comment for alvin :)
//test comment for alvin p 2 :)

// TO DO LIST (MIN REQS) ================================================= 
// (1) add the moving PIC-man character, WASD control, and enforce dead space
// (2) initialize basic maze and see if its visible on the TFT
//      fix intersection plotting and save previous direction
//      fixing dots array - change to mutable
// (3) add a moving ghost, PICMAN is target tile 
// (4) keep track of collisions and lost lives
// (5) add the other ghosts  w personality path logic 
// (6) add frighten mode w ghost return and release w appropriate counters
// (7) game over screen, points counter and bonus fruit, adjust graphics

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
int dotsMunched = 0; // maze is 244 dots, used when level is complete
int fruitxtile, fruitytile; 



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
int prevBDirection; //blinky
int prevPDirection; //pinky
int prevIDirection; //inky
int prevCDirection; //CLYDE we stan
int oppBDirection;  //store direction opposite to Blinky's current direction, useful bc ghosts cannot reverse
int oppPDirection;  //pinky
int oppIDirection;  //inky
int oppCDirection;  //clyde, loml
int prev_xBtile = 14; //calculated from (xtile-8)/8
int prev_yBtile = 14; //calculated from (ytile-16)/8
int P_xtarget;      //ghost target tiles, updated every animation loop based on picmans position
int P_ytarget;      //Blnky's target tile is picman and we just didnt create a separate variable 
int I_xtarget;
int I_ytarget;
int C_xtarget;
int C_ytarget;

int Blinky_Color = ILI9340_RED;
int Pinky_Color = ILI9340_PINK;
int Inky_Color = ILI9340_CYAN;
int Clyde_Color = ILI9340_ORANGE;

//lost life, game over, new level etc
int i; int ii; int jj; //because for loops r everywhere
int score;
int lives = 3;
int flashFlag = 0; // if collision: if high, plot picman, if low, plot background color
int flashNum = 0; //keep track of how many times picman is flashed after collision,stop at 4x    
float flashCounter = 0; // to slow down animation speed of picman death
int collisionFlag = 0; //set to high when a collision happens to pause characters
int gameOverFlag = 0; //seems redundant bc we already have isStart but useful for plotting end of game, new game stuff
int numLevels = 0; //how many levels have been cleared so far. Max? like 3 maybe? 


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

// === Timer Thread: CONTROLS GHOST MODES ======================================
// update a 1 second tick counter
static PT_THREAD (protothread_timer(struct pt *pt))
{
    PT_BEGIN(pt);
    //tft_setCursor(200, 15);
    //tft_setTextColor(ILI9340_WHITE);  tft_setTextSize(2);
    //tft_writeString("Time in seconds since boot\n");
    while(1) {
        PT_YIELD_TIME_msec(1000); // yield time 1 second
        // chase timers reset after pacman loses a life
        // ghosts reverse directions for mode changes EXCEPT when returning from frighten mode
        if (isStart==1 && ghostArray[0]!=3){ //if game is started via GUI and ghosts are not in frightened mode
            //0->in pen, 1->chase, 2->scatter, 3->frightened
            chaseTimer++; //increment timer to keep track of how long we've been in chase mode
            // ONLY increments if not in frightened mode !! nice 
            
            int i;
            if (chaseTimer<7){ //ghosts start in scatter mode, first scatter lasts 7 s
                for (i=0;i<4;i++){ // for all four ghosts
                    if (ghostArray[i]!=0){ //if ghost is not in monster pen
                        ghostArray[i]=2;   //ghosts start in scatter1
                    }
                }
            }
            else if (chaseTimer<27){ //go to chase mode after scatter1 for 7s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghost is not in monster pen
                        ghostArray[i]=1;   //change ghosts back to chase
                    }
                }
            }
            else if (chaseTimer<34){ //scatter2 for 7s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen
                        ghostArray[i]=2;   //change ghosts from chase to scatter2
                    }
                }
            }
            else if (chaseTimer<54){ //chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen 
                        ghostArray[i]=1;   //change ghosts back to chase
                    }
                }
            }
            else if (chaseTimer<59){ //scatter3 for 5s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ // if ghosts not in monster pen
                        ghostArray[i]=2;   //scatter3
                    }
                }
            }
            else if (chaseTimer<79){       //chase mode for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ // if ghosts not in monster pen
                        ghostArray[i]=1;   //chase mode
                    }
                }
            }
            else if (chaseTimer<84){      //scatter4 for 5s after chase for 20s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in monster pen
                        ghostArray[i]=2;   //scatter4
                    } 
                }
            }
            else {
                for (i=0;i<4;i++){   //after scatter4, stay in chase
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
            }
        }
        else if (isStart==1 && ghostArray[0]==3){ // if game is started and blinky is in frightened
            frightTimer++; //increment timer that keeps track of how long we've been in frighten mode
            int i;
            if (frightTimer>6) { //frighten mode lasts 6s
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){ //if ghosts not in pen, return them to previouse state
                        //DEAL WITH THIS LATER
                        ghostArray[i]=prevState[i];//remember to save prev state and change here, ie return to scatter or chase from frighten
                    }
                }
                Blinky_Color = ILI9340_RED;
                Pinky_Color = ILI9340_PINK;
                Inky_Color = ILI9340_CYAN;
                Clyde_Color = ILI9340_ORANGE;
                
                frightTimer=0; //reset frighten timer 
            }
        }
        //tft_setCursor(200, 15);
        //tft_write(sys_time_seconds);
        //sprintf(tft_str_buffer,"%d", sys_time_seconds); 
        //tft_printLine(1, 12, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK, 2);
        //tft_printLine(18, 5, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
    } // END WHILE(1)
    PT_END(pt);
} // timer thread

// === NEW LEVEL ===============================================================
void newlevel() {
    
    //reset counters
    numLevels++;
    dotsMunched = 0;
    global_dotCounter =0;
    PdotCounter = 0;
    IdotCounter = 0;
    CdotCounter = 0; // maze is 244 dots
    
    //reset map and the kids
    resetMap();
    resetGhosts();
}

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

// === RESET GHOSTS FUNCTION ========================================================
void resetGhosts() {
    tft_fillCircle(xPacman,yPacman,3,ILI9340_BLACK); //remove the ghosts              
    tft_fillCircle(xBlinky,yBlinky,2,ILI9340_BLACK); 
    tft_fillCircle(xPinky,yPinky,2,ILI9340_BLACK);
    tft_fillCircle(xInky,yInky,2,ILI9340_BLACK);
    tft_fillCircle(xClyde,yClyde,2,ILI9340_BLACK); 

    ghostArray[0] = 2; //put blinky in scatter mode
    for (ii=1;ii<4;ii++){ //set other ghost states to "in pen"
        ghostArray[ii]=0;
    }
    direction = 5; //not WASD so picman stops moving
    xPacman =120; 
    yPacman =228;
    xBlinky = 120; //blinky starts just above pen, in scatter mode
    yBlinky = 132; //other ghosts are in pen
    xPinky = 120;
    yPinky = 156;
    xInky = 105;
    yInky = 156;
    xClyde = 137;
    yClyde = 156;
    
    //set ghost colors to black so that when a game ends and the animation thread finishes it replots all characters but u cant see them 
    if (lives == 0){
        Blinky_Color = ILI9340_BLACK; 
        Pinky_Color = ILI9340_BLACK;
        Inky_Color = ILI9340_BLACK;
        Clyde_Color = ILI9340_BLACK; //clyde <3
    }
    else {
        Blinky_Color = ILI9340_RED; //reset ghosts to og colors
        Pinky_Color = ILI9340_PINK;
        Inky_Color = ILI9340_CYAN;
        Clyde_Color = ILI9340_ORANGE; //c l y d e <333
    }
    chaseTimer = 0; //reset timer for ghost behavior (scatter/chase timer)
 } // end of resetGhosts function

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
                
                if(dotsMunched >= 70){
                    //fruit!!
                    //fruitflag = 1;
                    tft_fillCircle(120, 176, 3, ILI9340_RED); //cherries? lol
                    fruitxtile = (120-8)/8; //we centered the maze on the TFT. subtract centering offset and divide by 8 to get tile
                    fruitytile = (176 - 16)/8; 
                    //dots[fruitxtile]

                }
                if (dotsMunched == 244){
                    //characters pause and picman flashes
                    while (flashNum < 6) { //flashNum initialized to zero
                        PT_YIELD_TIME_msec(300); //this is here to slow down the death animation
                            if(flashFlag == 0){ // plot over picman to flash   
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
                    flashNum = 0;
                    newlevel();
                    
                }
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
            }
            else if (dots[current_ytile][current_xtile]==2){ //if current tile contains a big dot
                score+=50; // increase points 
                dotsMunched++; //increase dots counter. max 244
                if (dotsMunched == 244){ //check if maze was cleared
                    //characters pause and picman flashes
                    while (flashNum < 6) { //flashNum initialized to zero
                        PT_YIELD_TIME_msec(300); //this is here to slow down the death animation
                            if(flashFlag == 0){ // plot over picman to flash   
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
                    flashNum = 0;
                    newlevel();
                }
                
                dots[current_ytile][current_xtile]=0; //store new dot value
                int i;
                for (i=0;i<4;i++){ //trigger frighten mode
                    if (ghostArray[i]!=0){ //if ghosts not in pen 
                        prevState[i]=ghostArray[i]; //store previous mode for when frightened is over
                        ghostArray[i]=3; //doin me a frighten 
                    }
                }
                
                Blinky_Color = ILI9340_BLUE;
                Pinky_Color = ILI9340_BLUE;
                Inky_Color = ILI9340_BLUE;
                Clyde_Color = ILI9340_BLUE;
               
                //tft_fillCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 4, ILI9340_WHITE);
                tft_fillCircle((short)(12+current_xtile*8),(short)(20+current_ytile*8),3,ILI9340_BLACK);  //erase Big Dot
                sprintf(tft_str_buffer,"%d", score); //print new score
                tft_printLine(2, 8, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2); 
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
                P_xtarget=xPacman-32; //4 tiles
                P_ytarget=yPacman-32;
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
                P_xtarget=xPacman-32; //4 tiles
                P_ytarget=yPacman;
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
                P_xtarget=xPacman; //4 tiles
                P_ytarget=yPacman+32;
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
                P_xtarget=xPacman+32; //4 tiles
                P_ytarget=yPacman;
            }//end pac-man arrow key logic
    
            ////////////// BLINKY /////////////////////////////////////
            int currentxBlinky = xBlinky; //pixel position
            int currentyBlinky = yBlinky;
            int currentxPinky = xPinky;
            int currentyPinky = yPinky;
            int currentxInky = xInky;
            int currentyInky = yInky;
            
            int current_xBtile = (xBlinky-8)/8; //find blinky's tile to check collisions and intersection behavior
            int current_yBtile = (yBlinky - 16)/8;
            int current_xPtile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
            int current_yPtile = (yPinky - 16)/8;
            int current_xItile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
            int current_yItile = (yPinky - 16)/8;
            
            int new_xBtile; //to check if intended tile is legal
            int new_yBtile; 
            int new_xPtile; //to check if intended tile is legal
            int new_yPtile; 
            
            int xBlinkyNext=xBlinky;
            int yBlinkyNext=yBlinky;
            int xPinkyNext=xPinky;
            int yPinkyNext=yPinky;
            
            if (ghostArray[0] == 1){ //if blinky is in chase mode 
            //blinky goes left at the start of the game 
            //if run into wall, or if next tile is dead space, then change directions 
                if (Bdirection==1) { //up
                    yBlinky-=1;
                    oppBDirection = 3; //down
                    yBlinkyNext -= 8; // add 8 because we care about the next tile 
                    if(prevBDirection == 2 || prevBDirection == 4){
                        xBlinky=current_xBtile*8+8+4;
                    }
                }
                else if (Bdirection==2) { //left
                    xBlinky-=1;
                    oppBDirection = 4; //right
                    xBlinkyNext -= 8; // add 8 because we care about the next tile 
                    if (prevBDirection==1 || prevBDirection==3){//check if turned from left/right
                        yBlinky=current_yBtile*8+16+4;
                    }
                }
                else if (Bdirection==3) { //down
                    yBlinky+=1;
                    oppBDirection = 1; //up
                    yBlinkyNext += 8; // add 8 because we care about the next tile 
                    if (prevBDirection==2 || prevBDirection==4){//check if turned from left/right
                        xBlinky=current_xBtile*8+8+4;
                    }
                }
                else if (Bdirection==4) { //right
                    xBlinky+=1;
                    oppBDirection = 2; //left
                    xBlinkyNext += 8; // add 8 because we care about the next tile
                    if (prevBDirection==1 || prevBDirection==3){//check if turned from left/right
                        yBlinky=current_yBtile*8+16+4;
                    }
                }
                int next_xBtile = (xBlinky-8)/8; //find blinky's tile to check collisions and intersection behavior
                int next_yBtile = (yBlinky - 16)/8;
                
                //only calculate next tile if we havent yet
                if ((next_xBtile!=current_xBtile || next_yBtile!=current_yBtile)){
                    //new_xBtile = (xBlinkyNext-8)/8; //solve for intended tile
                    //new_yBtile = ((yBlinkyNext-4) - 16)/8;

                    //Assess intended tile, check if tiles in the three potentially allowed directions are legal
                    // only three potentially legal tiles bc we cannot reverse directions 
                    int ii;
                    int tilesum; //if greater than 1, then there are multiple legal tiles available
                    float nextnexttileDist [4]; //to check which of the three other directions are legal
                    float shortestDist=1000;
                    int tempBDirection;
                    for (ii=1; ii<=4; ii++){
                        int xBlinkyNextNext=xBlinkyNext;
                        int yBlinkyNextNext=yBlinkyNext;
                        if(ii != oppBDirection){
                            if (ii==1) { //up
                                yBlinkyNextNext -= 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==2) { //left
                                xBlinkyNextNext -= 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==3) { //down
                                yBlinkyNextNext += 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==4) { //right
                                xBlinkyNextNext += 8; // add 8 because we care about the next tile
                            }
                            new_xBtile = (xBlinkyNextNext-8)/8; //solve for one of the three NEXT intended tiles
                            new_yBtile = ((yBlinkyNextNext-4) - 16)/8;
                            if(map[new_yBtile][new_xBtile] == 1){ //if the next intended tile is legal
                                int x_dist = abs(xPacman - xBlinkyNextNext); //calculate dist to target
                                int y_dist = abs(yPacman - yBlinkyNextNext);
                                float dist = max(x_dist, y_dist) + min(x_dist, y_dist)*.4;
                                if (dist<shortestDist) { //check which dir is shortest
                                    shortestDist=dist;
                                    prevBDirection  = Bdirection;
                                    tempBDirection=ii; //save direction
                                }
                            }
                        } //end if != oppbdirection
                    } // end for loop for the four directions 
                    Bdirection=tempBDirection;
                } //end if not same tile
                
                if(PdotCounter == 1 || (lives < 3 && global_dotCounter == 7)){
                    xPinky = 120; //move pinky above pen when counter limit is reached
                    yPinky = 132; 
                   
                    current_xPtile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
                    current_yPtile = (yPinky - 16)/8;
                    PdotCounter = 2;
                }  
                
                // *****PINKY********
                if (Pdirection==1) { //up
                    yPinky-=1;
                    oppPDirection = 3; //down
                    yPinkyNext -= 8; // add 8 because we care about the next tile 
                    if(prevPDirection == 2 || prevPDirection == 4){
                        xPinky=current_xPtile*8+8+4;
                    }
                }
                else if (Pdirection==2) { //left
                    xPinky-=1;
                    oppPDirection = 4; //right
                    xPinkyNext -= 8; // add 8 because we care about the next tile 
                    if (prevPDirection==1 || prevPDirection==3){//check if turned from left/right
                        yPinky=current_yPtile*8+16+4;
                    }
                }
                else if (Pdirection==3) { //down
                    yPinky+=1;
                    oppPDirection = 1; //up
                    yPinkyNext += 8; // add 8 because we care about the next tile 
                    if (prevPDirection==2 || prevPDirection==4){//check if turned from left/right
                        xPinky=current_xPtile*8+8+4;
                    }
                }
                else if (Pdirection==4) { //right
                    xPinky+=1;
                    oppPDirection = 2; //left
                    xPinkyNext += 8; // add 8 because we care about the next tile
                    if (prevPDirection==1 || prevPDirection==3){//check if turned from left/right
                        yPinky=current_yPtile*8+16+4;
                    }
                }
                int next_xPtile = (xPinky-8)/8; //find blinky's tile to check collisions and intersection behavior
                int next_yPtile = (yPinky - 16)/8;

                //only calculate next tile if we havent yet
                if (next_xPtile!=current_xPtile || next_yPtile!=current_yPtile){
                    //new_xBtile = (xBlinkyNext-8)/8; //solve for intended tile
                    //new_yBtile = ((yBlinkyNext-4) - 16)/8;

                    //Assess intended tile, check if tiles in the three potentially allowed directions are legal
                    // only three potentially legal tiles bc we cannot reverse directions 
                    int ii;
                    int tilesum; //if greater than 1, then there are multiple legal tiles available
                    float nextnexttileDist [4]; //to check which of the three other directions are legal
                    float shortestDist=1000;
                    int tempPDirection;
                    for (ii=1; ii<=4; ii++){
                        int xPinkyNextNext=xPinkyNext;
                        int yPinkyNextNext=yPinkyNext;
                        if(ii != oppPDirection){
                            if (ii==1) { //up
                                yPinkyNextNext -= 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==2) { //left
                                xPinkyNextNext -= 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==3) { //down
                                yPinkyNextNext += 8; // add 8 because we care about the next tile 
                            }
                            else if (ii==4) { //right
                                xPinkyNextNext += 8; // add 8 because we care about the next tile
                            }
                            new_xPtile = (xPinkyNextNext-8)/8; //solve for one of the three NEXT intended tiles
                            new_yPtile = ((yPinkyNextNext) - 16)/8;
                            if(map[new_yPtile][new_xPtile] == 1){ //if the next intended tile is legal
                                int x_dist = abs(P_xtarget - xPinkyNextNext); //calculate dist to target
                                int y_dist = abs(P_ytarget - yPinkyNextNext);
                                float dist = max(x_dist, y_dist) + min(x_dist, y_dist)*.4;
                                if (dist<shortestDist) { //check which dir is shortest
                                    shortestDist=dist;
                                    prevPDirection  = Pdirection;
                                    tempPDirection=ii; //save direction
                                }
                            }
                        } //end if != oppbdirection
                    } // end for loop for the four directions 
                    Pdirection=tempPDirection;
                } //end if not same tile 
            } //end if chase mode 

           
            ///////INKY///////
            /*
            if(IdotCounter == 31 || (lives < 3 && global_dotCounter == 17)){
                    xInky = 121; //move pinky above pen when counter limit is reached
                    yInky = 132; 
                   
                    current_xItile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
                    current_yItile = (yPinky - 16)/8;
                    IdotCounter = 32;
            }  
            
            ////////CLYDE/////// <3 
            if(CdotCounter == 61 || (lives < 3 && global_dotCounter == 32)){
                    xClyde = 121; //move pinky above pen when counter limit is reached
                    yClyde = 132; 
                   
                    current_xCtile = (xPinky-8)/8; //find pinky's tile to check collisions and intersection behavior
                    current_yCtile = (yPinky - 16)/8;
                    CdotCounter = 32;
            }  
            
          
            
             */ 
            ////////// PINKY &CO ////////////////////////////////////////////////
            // though tbh i think all of the local var should be moved to the top of the animation thread
            //int currentxPinky = xPinky; //pixel position
            //int currentyPinky = yPinky;
            currentxInky = xInky; //pixel position
            currentyInky = yInky;
            int currentxClyde = xClyde; //pixel position
            int currentyClyde = yClyde;
            //int current_xPtile = (xPinky-8)/8; 
            //int current_yPtile = (yPinky - 16)/8;
            current_xItile = (xInky-8)/8; 
            current_yItile = (yInky - 16)/8;
            int current_xCtile = (xClyde-8)/8; 
            int current_yCtile = (yClyde - 16)/8;
            
            ////////// CHECK FOR COLLISIONS ////////////////////////////////
            // do this after tiles have been updated for all characters
            // could use for OR operators and do this all at once but realllllly long if condition 
            
            if(current_xtile == current_xBtile && current_ytile == current_yBtile){
                if(ghostArray[0] != 3){ //if not in frighten mode
                    lives -= 1; //lose a life rip
                    // all characters pause and picman dies
                    collisionFlag = 1;
                }
                else{ 
                    Blinky_Color = ILI9340_RED; //when frighten mode triggered, blinky is set to blue. replot in red once Munched(tm)
                    xBlinky = 120; // plot blinky in OG position
                    yBlinky = 132;
                    ghostArray[0] = prevState[0]; // put him back in whatever mode he was in before being Frightened 
                }
            } // end blinky collision check
            else if(current_xtile == current_xPtile && current_ytile == current_yPtile){
                if(ghostArray[1] != 3){
                    lives -= 1; //lose a life rip
                    collisionFlag = 1;
                }
                else{
                    printf("ghost state = %d, \n", ghostArray[1]);
                    Pinky_Color = ILI9340_PINK;
                    xPinky = 120;
                    yPinky = 132;
                    ghostArray[1] = prevState[1];
                    
                }
            } // end pinky collision check
            
            // IF collision AND not in frighten mode
            // all characters pause, picman dies (flashing)
            // picman doesnt move until gui input again 
            // ghosts are reset, timer for ghost modes is reset 
            if (collisionFlag == 1){   //if collision occurs, animate death and replot   
            // in game, ms pacman kinda warps into nothing but we dont have that resolution so im just going to have her flash        
               
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
            
            
            tft_fillCircle(currentxPacman,currentyPacman,3,ILI9340_BLACK); //erase pic-man
            tft_fillCircle(currentxBlinky,currentyBlinky,2,ILI9340_BLACK); //erase blinky
            tft_fillCircle(currentxPinky,currentyPinky,2,ILI9340_BLACK); //erase pinky
            tft_fillCircle(currentxInky,currentyInky,2,ILI9340_BLACK); //erase inky
            tft_fillCircle(currentxClyde,currentyClyde,2,ILI9340_BLACK); //erase clyde rip loml

            tft_fillCircle(xPacman,yPacman,3,ILI9340_YELLOW); //plot new picman              
            tft_fillCircle(xBlinky,yBlinky,2,Blinky_Color); //plot new blinky
            tft_fillCircle(xPinky,yPinky,2,Pinky_Color); //plot new pinky
            tft_fillCircle(xInky,yInky,2,Inky_Color); //plot new inky
            tft_fillCircle(xClyde,yClyde,2,Clyde_Color); //plot new clyde! loml is back 
            
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
            printf("rip");
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
        // clear flag
        new_arrow = 0;  
        if (arrow_value==1){
            direction = arrow_id;
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

