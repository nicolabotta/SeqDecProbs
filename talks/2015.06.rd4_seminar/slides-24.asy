if(!settings.multipleView) settings.batchView=false;
settings.tex="pdflatex";
defaultfilename="slides-24";
if(settings.render < 0) settings.render=4;
settings.outformat="";
settings.inlineimage=true;
settings.embed=true;
settings.toolbar=false;
viewportmargin=(2,2);

size(6cm);
include graph;
string[] xs = {"a","b","c","d","e"};
string[] path = {"a","b","c","d","d","d","c","b"};
string[] cr = {"7","1","3","5","4","7","8","8"};
int nc = xs.length;
int nt = path.length;
real x0 = 0.0;
real t0 = 0.0;
real dx = 0.1;
real dt = 0.1;
real x;
real t;
pair A, B, C, D;
defaultpen(2);
for (int j = 0; j < nc; ++j) {
x = x0 + j * dx;
label(xs[j], (x+dx/2,t0-dt));
}
for (int i = 0; i < nt; ++i) {
x = x0;
t = t0 + i * dt;
label((string) i, (x-dx,t+dt/2));
for (int j = 0; j < nc; ++j) {
x = x0 + j * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
if (i == 3 && j < nc - 1) fill(A--B--C--D--A--cycle);
if (i == 6 && j > nc - 3) fill(A--B--C--D--A--cycle);
draw(A--B--C--D--A, grey);
}
}
x = x0;
t = t0 + (0 + nt) * dt + dt/2;
label("...", (x-dx,t+dt/2));
label("...", (x+nc*dx/2,t+dt/2));
x = x0;
t = t0 + (1 + nt) * dt + dt;
label("n", (x-dx,t+dt/2));
for (int j = 0; j < nc; ++j) {
x = x0 + j * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
draw(A--B--C--D--A, grey);
}
int steps = 0;
t = t0 + steps * dt;
x = x0 + 2 * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
draw(A--B--C--D--A, lightred);
int steps = 1;
t = t0 + steps * dt;
x = x0 + 1 * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
draw(A--B--C--D--A, red);
viewportsize=(119.84285pt,0);
