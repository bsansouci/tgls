#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/fail.h>

#include <OpenGL/Gl.h>

// CAMLprim value TglClearColor(value r, value g, value b, value a) {
//   CAMLparam4(r, g, b, a);
//   glClearColor();
//   CAMLreturn0;
// }

CAMLprim value TglCreateProgram() {
  CAMLparam0();
  CAMLreturn(glCreateProgram());
}

CAMLprim value TglCreateShader(value shaderType) {
  CAMLparam1(shaderType);
  CAMLreturn(glCreateShader(Int_val(shaderType)));
}

void TglAttachShader(value program, value shader) {
  CAMLparam2(program, shader);
  glAttachShader(Int_val(program), Int_val(shader));
  CAMLreturn0;
}

void TglDeleteShader(value shader) {
  CAMLparam1(shader);
  glDeleteShader(Int_val(shader));
  CAMLreturn0;
}

void TglShaderSource(value shader, value stringArray) {
  CAMLparam2(shader, stringArray);
  int numOfElements = Wosize_val(stringArray);
  const char **arrOfElements = malloc(sizeof(char *) * numOfElements);
  int *arrOfLengths = malloc(sizeof(int) * numOfElements);
  for(int i = 0; i < numOfElements; ++i) {
    value e = Field(stringArray, i);
    arrOfElements[i] = String_val(e);
    arrOfLengths[i] = caml_string_length(e);
  }
  glShaderSource(Int_val(shader), numOfElements, arrOfElements, arrOfLengths);
  CAMLreturn0;
}

void TglCompileShader(value shader) {
  CAMLparam1(shader);
  glCompileShader(Int_val(shader));
  CAMLreturn0;
}

void TglLinkProgram(value program) {
  CAMLparam1(program);
  glLinkProgram(program);
  CAMLreturn0;
}

void TglUseProgram(value program) {
  CAMLparam1(program);
  glUseProgram(program);
  CAMLreturn0;
}

CAMLprim value TglGenBuffers(value count) {
  CAMLparam1(count);
  CAMLlocal1(ret);
  unsigned int buffers[count];
  glGenBuffers(count, &buffers);

  ret = caml_alloc_small(count, 0);
  for (int i = 0; i < count; ++i) {
    Field(ret, i) = Val_int(buffers[i]);
  }
  CAMLreturn(ret);
}

void TglClearColor(value r, value g, value b, value a) {
  CAMLparam4(r, g, b, a);
  glClearColor(Int_val(r), Int_val(g), Int_val(b), Int_val(a));
  CAMLreturn0;
}
