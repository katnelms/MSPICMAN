/*
 * File:        Python control for ECE 4760 Final Project: Ms PIC-MAN
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

// timer stuff
// pic is 240 pixels x 320 pixels, scale is appropriate
// pg 162 of pic32 manual, timer period is an int  
int TIMEOUT = 800000;// For ISR, but only if we get to adding music

int chaseTimer;
int frightTimer;
char isStart;
int button_check;
int buttonCounter;
int begin_time, check_time, prevDirection;
short xPacman=120;
short yPacman=228;
short xBlinky=120;
short yBlinky=132;
char ghostArray[4]={2,0,0,0};//blinky,pinky,inky,clyde
                             //0->in pen, 1->chase, 2->scatter, 3->frightened
int ghostCounters[3];//pinky,inky,clyde
int prevState;

const char map[36][28]={
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
    };


char dots[36][28] = {
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


// character animation stuff
int direction; //takes in WASD or arrow key input to change PICMAN motion
int score;

////////////////////////////////////
// === print a line on TFT =====================================================
// print string buffer
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
void __ISR(_TIMER_3_VECTOR, ipl2) Timer3Handler(void)
{
    // you MUST clear the ISR flag
    mT3ClearIntFlag(); 
   
         
}

// second ISR, not for any particular purpose yet, just not sure if we need a
//32 bit timer or not so left both in for now 
void __ISR(_TIMER_4_VECTOR, ipl2) Timer4Handler(void) {
	mT4ClearIntFlag(); // you MUST clear the ISR flag
   
}

// === Timer Thread =================================================
// update a 1 second tick counter
static PT_THREAD (protothread_timer(struct pt *pt))
{
    PT_BEGIN(pt);
    //tft_setCursor(200, 15);
    //tft_setTextColor(ILI9340_WHITE);  tft_setTextSize(2);
    //tft_writeString("Time in seconds since boot\n");
    while(1) {
        // yield time 1 second
        PT_YIELD_TIME_msec(1000) ;
        if (isStart==1 && ghostArray[0]!=3){
            chaseTimer++;
            int i;
            if (chaseTimer<7){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=2;
                    }
                }
            }
            else if (chaseTimer<27){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
            }
            else if (chaseTimer<34){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=2;
                    }
                }
            }
            else if (chaseTimer<54){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
            }
            else if (chaseTimer<59){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=2;
                    }
                }
            }
            else if (chaseTimer<79){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
            }
            else if (chaseTimer<84){
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=2;
                    }
                }
            }
            else {
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=1;
                    }
                }
            }
        }
        else if (isStart==1 && ghostArray[0]==3){
            frightTimer++;
            int i;
            if (frightTimer>6) {
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        ghostArray[i]=prevState;//remember to save prev state and change here
                    }
                }
                frightTimer=0;
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


// === ANIMATION THREAD==================================================== //
//Declare boid initial position and velocity randomly
// loop through boids at each time step
// update velocity based on parameters input from python GUI
// use euler solver to update position
// animate at 30 fps 
                              
static PT_THREAD (protothread_animation (struct pt *pt)){
    PT_BEGIN(pt);
    while(1){
        begin_time = PT_GET_TIME();  // objective animation speed 30FPS
        tft_drawCircle(xPacman,yPacman,3,ILI9340_BLACK); //pic-man
        tft_drawCircle(xBlinky,yBlinky,2,ILI9340_BLACK); //blinky
        int current_xtile = (xPacman-8)/8;
        int current_ytile = (yPacman - 16)/8;
        //int remainderX=current_xtile%8;
        //int remainderY=current_ytile%8;
        if (isStart==1){
            if(dots[current_ytile][current_xtile]==1){
                score+=10;
                dots[current_ytile][current_xtile]=0;
                sprintf(tft_str_buffer,"  Score: %d  ", score);
                tft_printLine(18, 5, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
            }
            else if (dots[current_ytile][current_xtile]==2){
                score+=50;
                dots[current_ytile][current_xtile]=0;
                int i;
                for (i=0;i<4;i++){
                    if (ghostArray[i]!=0){
                        prevState=ghostArray[i];
                        ghostArray[i]=3;
                    }
                }
                //tft_drawCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 4, ILI9340_WHITE);
                tft_drawCircle((short)(12+current_xtile*8),(short)(20+current_ytile*8),4,ILI9340_BLACK);  
                sprintf(tft_str_buffer,"  Score: %d  ", score);
                tft_printLine(18, 5, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
            }

            int new_xtile;
            int new_ytile;
            /*move in direction*/
            if (direction==1) { //up
                yPacman-=1;
                if (yPacman<17)
                    yPacman=303;
                new_xtile = (xPacman-8)/8;
                new_ytile = ((yPacman-4) - 16)/8;
                //printf("new x = %d",new_xtile);
                //printf("new y = %d",new_ytile);
                if (map[new_ytile][new_xtile]==0){
                    if(yPacman==303)
                        yPacman=17;
                    else
                        yPacman+=1;
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
            else if (direction==2) { //left
                xPacman-=1;
                if (xPacman<10) //wrap
                    xPacman=228;
                new_xtile = ((xPacman-4)-8)/8;
                new_ytile = (yPacman - 16)/8;
                //printf("new x = %d\n",new_xtile);
                //printf("new y = %d\n",new_ytile);
                if (map[new_ytile][new_xtile]==0) {
                    //printf("in if\n");
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
            else if (direction==3) { //down
                yPacman+=1;
                if (yPacman>303)
                    yPacman=17;
                new_xtile = (xPacman-8)/8;
                new_ytile = ((yPacman+4) - 16)/8;
                if (map[new_ytile][new_xtile]==0) {
                    if(yPacman==17)
                        yPacman=303;
                    else
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
            else if (direction==4) { //right
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
            
            
            
        }
        tft_drawCircle(xPacman,yPacman,3,ILI9340_MAGENTA);              
        tft_drawCircle(xBlinky,yBlinky,2,ILI9340_RED); //blinky
        
        // 30 fps => frame time of 32 mSec
        check_time = PT_GET_TIME() - begin_time; //checks if more than 32 msec has passed
        if(check_time > 17)
            mPORTAClearBits(BIT_0); // turn off LED if below 30FPS
        else{
            mPORTASetBits(BIT_0); // turn LED on IF we meet 30FPS 
        }
        
        int i;
        for(i = 0; i < 4; i++){
            
        }
        
        PT_YIELD_TIME_msec(17 - check_time);   
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
        //tft_drawCircle(280,200,5,ILI9340_MAGENTA);
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
        /*
        // toggle switch
        if (PT_term_buffer[0]=='t'){
            // signal the button thread
            new_toggle = 1;
            // subtracting '0' converts ascii to binary for 1 character
            toggle_id = (PT_term_buffer[1] - '0')*10 + (PT_term_buffer[2] - '0');
            toggle_value = PT_term_buffer[3] - '0';
        }
        
        // slider
        if (PT_term_buffer[0]=='s'){
            sscanf(PT_term_buffer, "%c %d %f", &junk, &slider_id, &slider_value);
            new_slider = 1;
        }
        
        // listbox
        if (PT_term_buffer[0]=='l'){
            new_list = 1;
            list_id = PT_term_buffer[2] - '0' ;
            list_value = PT_term_buffer[3] - '0';
            //printf("%d %d", list_id, list_value);
        }
        
        // radio group
        if (PT_term_buffer[0]=='r'){
            new_radio = 1;
            radio_group_id = PT_term_buffer[2] - '0' ;
            radio_member_id = PT_term_buffer[3] - '0';
            //printf("%d %d", radio_group_id, radio_member_id);
        }
        */
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
    //timeout is 40kHz, leftover from lab 4, adjust accordinly
    int TIMEOUT4 = 40000000/40000; 
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
    for(draw_row =0; draw_row < 36; draw_row++){
        int check_tile = 0;
        for(check_tile = 0; check_tile < 28; check_tile++){
            if(map[draw_row][check_tile] == 0){
                tft_fillRect((short) (8 + check_tile*8), (short) (16 + draw_row*8), (short) 8, (short) 8, ILI9340_BLUE);
            }
            if(dots[draw_row][check_tile] == 1)
                tft_drawPixel((short)(12 + check_tile*8), (short) (20 + draw_row*8), ILI9340_WHITE);
            else if(dots[draw_row][check_tile] == 2)
                tft_drawCircle((short)(12 + check_tile*8), (short) (20 + draw_row*8),(short) 4, ILI9340_WHITE);
        }
    }
    sprintf(tft_str_buffer,"  Score: %d  ", score);
    tft_printLine(18, 5, tft_str_buffer, ILI9340_MAGENTA, ILI9340_BLACK,2);
  
  
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

