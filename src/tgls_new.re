type programT;

external glCreateProgram : unit => programT = "TglCreateProgram";

type shaderT;

external createShader : shaderType::int => shaderT = "TglCreateShader";

external attachShader : programT => shaderT => unit = "TglAttachShader";

external deleteShader : shaderT => unit = "TglDeleteShader";

external shaderSource : shaderT => array string => unit = "TglShaderSource";

external compileShader : shaderT => unit = "TglCompileShader";

external linkProgram : programT => unit = "TglLinkProgram";

external useProgram : programT => unit = "TglUseProgram";

type bufferT;

external genBuffers : num::int => array bufferT = "TglGenBuffers";
external clearColor : red::int => green::int => blue::int => alpha::int => unit = "TglClearColor";
