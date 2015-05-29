if(!settings.multipleView) settings.batchView=false;
settings.tex="pdflatex";
defaultfilename="slides-10";
if(settings.render < 0) settings.render=4;
settings.outformat="";
settings.inlineimage=true;
settings.embed=true;
settings.toolbar=false;
viewportmargin=(2,2);

include graph;
size(11cm);
int o = 1;
int l = 8;
int h = 4;
pair A, B, C, D;
int x = 0;
real[] midxs1;
real[] midys1;
real[] midxs2;
real[] midys2;
for (int i = 0; i < 6; ++i)
{
x = i * (l + o);
midxs1.push(x + l/2);
midys1.push(0);
if (i == 3)
{
real a = (l+2*o)/3;
for (int j = 1; j < 4; ++j)
{
draw(Circle((x-2*o+j*a-0.5,2),.5), blue);
}
} else
{
A=(x,0); B=(x,h); C=(x+l,h); D=(x+l,0);
if (i == 1) {
fill(A--B--C--D--cycle,blue);
} else {
draw(A--B--C--D--A,blue);
}
}
}
int cx = l+o+floor(l/2);
int cy = h + h + h;
int cr = floor(h);
draw(Circle((cx,cy),cr), blue);
fill(Circle((cx-1.5,cy-1.5),0.5), green);
draw(Circle((cx+2,cy+2),0.5), yellow);
draw(Circle((cx-0.2,cy+1.5),0.5), brown);
draw(Circle((cx+1.8,cy-1.2),0.5), red);
draw(Circle((cx-2.1,cy+1.2),0.5), black);
label("n+1 steps left", (x+17,2));
int y = -15;
for (int i = 0; i < 6; ++i)
{
x = i * (l + o);
midxs2.push(x + l/2);
midys2.push(y+h);
if (i == 3)
{
real a = (l+2*o)/3;
for (int j = 1; j < 4; ++j)
{
draw(Circle((x-2*o+j*a-0.5,2+y),.5), blue);
}
} else
{
A=(x,y); B=(x,y+h); C=(x+l,y+h); D=(x+l,y);
if (i == 0 | i == 5)
{
draw(A--B--C--D--A,white);
} else
{
draw(A--B--C--D--A,blue);
}
}
}
label("n steps left", (x+17,y+2), black);
for (int j = 1; j < 5; ++j)
{
draw((midxs1[1],midys1[1])--(midxs2[j],midys2[j]), red,
EndArrow);
}


viewportsize=(307.28987pt,0);
