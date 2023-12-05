#!/bin/bash

# Verificar si se proporcionó un argumento
if [ -z "$1" ]; then
  echo "Debe proporcionar el nombre del archivo como argumento"
  exit 1
fi

# Asignar el argumento a una variable
archivo=$1
MAQUINA_DE_TRAZADOS_Y_COLORES_DIR="../laboratorios/LabSem10/maquina_de_trazados_Y_colores/lib/maquinaTrazados-v0.1.jar"

# Ejecutar el comando para compilar y correr el archivo
openjml --rac -cp "$MAQUINA_DE_TRAZADOS_Y_COLORES_DIR" Constants.java Utils.java "$archivo".java && openjml-java -cp "$MAQUINA_DE_TRAZADOS_Y_COLORES_DIR":. "$archivo"