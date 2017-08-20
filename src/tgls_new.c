#include <stdio.h>

#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/fail.h>
#include <caml/bigarray.h>

#include <OpenGL/Gl.h>

// CAMLprim value TglClearColor(value r, value g, value b, value a) {
//   CAMLparam4(r, g, b, a);
//   glClearColor();
//   CAMLreturn0;
// }

CAMLprim value TglCreateProgram() {
  CAMLparam0();
  CAMLreturn(Val_int(glCreateProgram()));
}

CAMLprim value TglCreateShader(value shaderType) {
  CAMLparam1(shaderType);
  CAMLreturn(Val_int(glCreateShader(Int_val(shaderType))));
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
  const GLchar **arrOfElements = malloc(sizeof(GLchar *) * numOfElements);
  GLint *arrOfLengths = malloc(sizeof(GLint) * numOfElements);
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
  glLinkProgram(Int_val(program));
  CAMLreturn0;
}

void TglUseProgram(value program) {
  CAMLparam1(program);
  glUseProgram(Int_val(program));
  CAMLreturn0;
}

CAMLprim value TglGenBuffers(value count) {
  CAMLparam1(count);
  CAMLlocal1(ret);

  int size = Int_val(count);
  unsigned int *buffers = malloc(sizeof(unsigned int) * size);
  glGenBuffers(size, buffers);

  ret = caml_alloc_small(size, 0);
  for (int i = 0; i < size; ++i) {
    Field(ret, i) = Val_int(buffers[i]);
  }
  CAMLreturn(ret);
}

CAMLprim value TglGenBuffer() {
  CAMLparam0();
  unsigned int buffers = 0;
  glGenBuffers(1, &buffers);
  CAMLreturn(Val_int(buffers));
}

void TglClearColor(value r, value g, value b, value a) {
  CAMLparam4(r, g, b, a);
  glClearColor(Double_val(r), Double_val(g), Double_val(b), Double_val(a));
  CAMLreturn0;
}

void TglBindBuffer(value kind, value buffer) {
  CAMLparam2(kind, buffer);
  glBindBuffer(Int_val(kind), Int_val(buffer));
  CAMLreturn0;
}

CAMLprim value TglGenTextures(value count) {
  CAMLparam1(count);
  CAMLlocal1(ret);

  int size = Int_val(count);
  unsigned int *textures = malloc(sizeof(unsigned int) * size);
  glGenTextures(size, textures);

  ret = caml_alloc_small(size, 0);
  for (int i = 0; i < size; ++i) {
    Field(ret, i) = Val_int(textures[i]);
  }

  CAMLreturn(ret);
}

CAMLprim value TglGenTexture() {
  CAMLparam0();
  unsigned int textures = 0;
  glGenTextures(1, &textures);
  CAMLreturn(Val_int(textures));
}

void TglActiveTexture(value textureUnit) {
  CAMLparam1(textureUnit);
  glActiveTexture(Int_val(textureUnit));
  CAMLreturn0;
}

void TglBindTexture(value kind, value texture) {
  CAMLparam2(kind, texture);
  glBindTexture(Int_val(kind), Int_val(texture));
  CAMLreturn0;
}

void TglTexSubImage2D_native(value target, value level, value xoffset, value yoffset, value width, value height, value format, value type, value pixels) {
  CAMLparam5(target, level, xoffset, yoffset, width);
  CAMLxparam4(height, format, type, pixels);
  
  glTexSubImage2D(Int_val(target), Int_val(level), Int_val(xoffset), Int_val(yoffset), Int_val(width), Int_val(height), Int_val(format), Int_val(type), Caml_ba_data_val(pixels));
  CAMLreturn0;
}

void TglTexSubImage2D_bytecode(value * argv, int argn) {
  TglTexSubImage2D_native(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
}


void TglTexParameteri(value kind, value pname, value param) {
  CAMLparam3(kind, pname, param);
  glTexParameteri(Int_val(kind), Int_val(pname), Int_val(param));
  CAMLreturn0;
}

void TglEnable(value thing) {
  CAMLparam1(thing);
  glEnable(Int_val(thing));
  CAMLreturn0;
}

void TglDisable(value thing) {
  CAMLparam1(thing);
  glDisable(Int_val(thing));
  CAMLreturn0;
}

void TglBlendFunc(value sfactor, value dfactor) {
  CAMLparam2(sfactor, dfactor);
  glBlendFunc(Int_val(sfactor), Int_val(dfactor));
  CAMLreturn0;
}

CAMLprim value TglReadPixels_RGBA(value x, value y, value width, value height) {
  CAMLparam4(x, y, width, height);
  CAMLlocal1(ret);

  // Allocate a pointer for caml_ba_alloc's sake.
  intnat *size = malloc(sizeof(intnat));
  *size = Int_val(width) * Int_val(height) * 4;

  char *data = malloc(*size * sizeof(char));

  glReadPixels(Int_val(x), Int_val(y), Int_val(width), Int_val(height), GL_RGBA, GL_UNSIGNED_BYTE, data);

  // return array of size `size` of dimension 1 of uint8 (char).
  ret = caml_ba_alloc(CAML_BA_UINT8, 1, data, size);
  CAMLreturn(ret);
}

void TglTexImage2D_RGBA_native(value target, value level, value width, value height, value border, value data) {
  CAMLparam5(target, level, width, height, border);
  CAMLxparam1(data);
  glTexImage2D(Int_val(target), Int_val(level), 4, Int_val(width), Int_val(height), Int_val(border), GL_RGBA, GL_UNSIGNED_BYTE, Caml_ba_data_val(data));
  CAMLreturn0;
}

void TglTexImage2D_RGBA_bytecode(value * argv, int argn) {
  TglTexImage2D_RGBA_native(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

void TglUniform1i(value location, value v) {
  CAMLparam2(location, v);
  glUniform1i(Int_val(location), Int_val(v));
  CAMLreturn0;
}

void TglUniform1f(value location, value v) {
  CAMLparam2(location, v);
  glUniform1f(Int_val(location), Double_val(v));
  CAMLreturn0;
}

void TglBufferData(value target, value data, value usage) {
  CAMLparam3(target, data, usage);
  glBufferData(Int_val(target), caml_ba_byte_size(Caml_ba_array_val(data)), Caml_ba_data_val(data), Int_val(usage));
  CAMLreturn0;
}

void TglViewport(value x, value y, value width, value height) {
  CAMLparam4(x, y, width, height);
  glViewport(Int_val(x), Int_val(y), Int_val(width), Int_val(height));
  CAMLreturn0;
}

void TglClear(value mask) {
  CAMLparam1(mask);
  glClear(Int_val(mask));
  CAMLreturn0;
}

CAMLprim value TglGetUniformLocation(value program, value name) {
  CAMLparam2(program, name);
  CAMLreturn(Val_int(glGetUniformLocation(Int_val(program), String_val(name))));
}

CAMLprim value TglGetAttribLocation(value program, value name) {
  CAMLparam2(program, name);
  CAMLreturn(Val_int(glGetAttribLocation(Int_val(program), String_val(name))));
}

void TglEnableVertexAttribArray(value attrib) {
  CAMLparam1(attrib);
  glEnableVertexAttribArray(Int_val(attrib));
  CAMLreturn0;
}

void TglVertexAttribPointer_native(value index, value size, value typ, value normalize, value stride, value offset) {
  CAMLparam5(index, size, typ, normalize, stride);
  CAMLxparam1(offset);
  long o = (long)Int_val(offset);
  glVertexAttribPointer(Int_val(index), Int_val(size), Int_val(typ), Bool_val(normalize), Int_val(stride), (const GLvoid *)o);
  CAMLreturn0;
}

void TglVertexAttribPointer_bytecode(value * argv, int argn) {
  TglVertexAttribPointer_native(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

CAMLprim value TglGetProgramiv(value program, value pname) {
  CAMLparam2(program, pname);
  GLint ret;
  glGetProgramiv(Int_val(program), Int_val(pname), &ret);
  CAMLreturn(Val_int(ret));
}

CAMLprim value TglGetShaderiv(value shader, value pname) {
  CAMLparam2(shader, pname);
  GLint ret;
  glGetShaderiv(Int_val(shader), Int_val(pname), &ret);
  CAMLreturn(Val_int(ret));
}

CAMLprim value TglGetShaderInfoLog(value shader) {
  CAMLparam1(shader);
  CAMLlocal1(ret);

  GLint exactLength;
  glGetShaderiv(Int_val(shader), GL_INFO_LOG_LENGTH, &exactLength);
  GLchar *buffer = malloc(exactLength * sizeof(char));
  glGetShaderInfoLog(Int_val(shader), exactLength - 1, NULL, buffer);

  ret = caml_copy_string(buffer);
  CAMLreturn(ret);
}

CAMLprim value TglGetProgramInfoLog(value program) {
  CAMLparam1(program);
  CAMLlocal1(ret);

  GLint exactLength;
  glGetProgramiv(Int_val(program), GL_INFO_LOG_LENGTH, &exactLength);

  GLchar *buffer = malloc(exactLength * sizeof(char));
  glGetProgramInfoLog(Int_val(program), exactLength - 1, NULL, buffer);
  ret = caml_copy_string(buffer);
  CAMLreturn(ret);
}

CAMLprim value TglGetShaderSource(value shader) {
  CAMLparam1(shader);
  CAMLlocal1(ret);

  GLint exactLength;
  glGetShaderiv(Int_val(shader), GL_SHADER_SOURCE_LENGTH, &exactLength);

  GLchar *buffer = malloc(exactLength * sizeof(char));
  glGetShaderSource(Int_val(shader), exactLength - 1, NULL, buffer);
  ret = caml_copy_string(buffer);
  CAMLreturn(ret);
}

void TglDrawArrays(value mode, value first, value count) {
  CAMLparam3(mode, first, count);
  glDrawArrays(Int_val(mode), Int_val(first), Int_val(count));
  CAMLreturn0;
}

void TglDrawElements(value mode, value first, value typ, value offset) {
  CAMLparam4(mode, first, typ, offset);
  long o = (long)Int_val(offset);
  glDrawElements(Int_val(mode), Int_val(first), Int_val(typ), (const GLvoid *)o);
  CAMLreturn0;
}

void TglUniformMatrix4fv(value location, value transpose, value val) {
  CAMLparam3(location, transpose, val);
  int size = Wosize_val(val);
  float *matrix = malloc(sizeof(float) * size);
  for (int i = 0; i < size; ++i){
    matrix[i] = Double_field(val, i);
  }
  glUniformMatrix4fv(Int_val(location), 1, Bool_val(transpose), matrix);
  CAMLreturn0;
}
