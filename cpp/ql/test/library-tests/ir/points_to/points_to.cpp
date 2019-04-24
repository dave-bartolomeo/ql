struct Point {
  int x;
  int y;
};

struct Base1 {
  int b1;
};

struct Base2 {
  int b2;
};

struct DerivedSI : Base1 {
  int dsi;
};

struct DerivedMI : Base1, Base2 {
  int dmi;
};

struct DerivedVI : virtual Base1 {
  int dvi;
};

void PointsTo(int a, Point& b, Point* c, int* d, DerivedSI* e, DerivedMI* f, DerivedVI* g) {
  int i = a;
  i = *&a;
  i = *(&a + 0);
  i = b.x;
  i = b.y;
  i = c->x;
  i = c->y;
  i = *d;
  i = *(d + 0);
  i = d[5];
  i = 5[d];
  i = d[a];
  i = a[d];

  int* p = &b.x;
  i = *p;
  p = &b.y;
  i = *p;
  p = &c->x;
  i = *p;
  p = &c->y;
  i = *p;
  p = &d[5];
  i = *p;
  p = &d[a];
  i = *p;

  Point* q = &c[a];
  i = q->x;
  i = q->y;

  i = e->b1;
  i = e->dsi;
  i = f->b1;
  i = f->b2;
  i = f->dmi;
  i = g->b1;
  i = g->dvi;
}