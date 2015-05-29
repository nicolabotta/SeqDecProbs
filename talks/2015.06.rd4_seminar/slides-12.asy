if(!settings.multipleView) settings.batchView=false;
settings.tex="pdflatex";
defaultfilename="slides-12";
if(settings.render < 0) settings.render=4;
settings.outformat="";
settings.inlineimage=true;
settings.embed=true;
settings.toolbar=false;
viewportmargin=(2,2);

size(6cm);
include graph;
string[] xs = {"a","b","c","d","e"};
string[] path = {"b","c","d","e","e","d","c","d"};
string[] cr = {"7","2","1","4","7","8","8","7"};
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
label(xs[j], position=(x+dx/2,t0-1.5*dt), align=N);
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
int steps = 7;
for (int i = 0; i < steps - 1; ++i) {
t = t0 + i * dt;
int j = search(xs,path[i]);
x = x0 + j * dx;
label(cr[i], (x+dx/2,t+dt/2), lightred);
}
if (steps > 0) {
t = t0 + (steps - 1) * dt;
int j = search(xs,path[steps - 1]);
x = x0 + j * dx;
label(cr[steps - 1], (x+dx/2,t+dt/2), lightred);
}
for (int i = 0; i < steps; ++i) {
t = t0 + i * dt;
int j = search(xs,path[i]);
x = x0 + j * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
draw(A--B--C--D--A, lightred);
}
t = t0 + steps * dt;
int j = search(xs,path[steps]);
x = x0 + j * dx;
A=(x,t); B=(x+dx,t); C=(x+dx,t+dt); D=(x,t+dt);
label("?", (x+dx/2,t+dt/2), red);
draw(A--B--C--D--A, red);
viewportsize=(307.28987pt,0);
