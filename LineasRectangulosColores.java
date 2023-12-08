import java.util.Random;
import java.awt.Font;
import java.util.Scanner;

public class LineasRectangulosColores {
    /******************************************************/
    /********************** GLOBALES **********************/
    /******************************************************/

    public static Scanner consola = new Scanner(System.in);

    /**
     * Constantes y variables para la configuracion del Panel
     */
    public static final int PANEL_BARRA_TITULO_ALTURA = 38; // alto de la barra de titulo 
    public static final int PANEL_DEFAULT_XMAX = 512;
    public static final int PANEL_DEFAULT_YMAX = 512;
    public static final String PANEL_DEFAULT_TITLE = "Lineas Rectangulos Colores (V 1.0.Beta)";
    
    public static int PANEL_YMAX = PANEL_DEFAULT_YMAX;
    public static int PANEL_XMAX = PANEL_DEFAULT_XMAX;

    /**
     * Alto y ancho aproximados de la fuente en pixeles
     */
    public static int ANCHO_FUENTE = 4; // font 8 -> 2, 12 -> 4, 24 -> 8
    public static int ALTO_FUENTE = 5; // font 8 -> 2, 12 -> 5, 24 -> 10

    /**
     * Constantes y variables para la configuracion del tablero
     */
    public static final int DEFAULT_TABLERO_SLOTS = 9;
    public static final int TABLERO_SLOTS = DEFAULT_TABLERO_SLOTS;
	public static int[][] tablero = new int[TABLERO_SLOTS][TABLERO_SLOTS];
    // Guardaram tamaño de tablero y posicion de esquina superior izquierda respectivamente
    public static int TABLERO_SIZE, TABLERO_X_POS, TABLERO_Y_POS;

    /**
     * Enum for objects representation in array indexes
     * constantes para la representacion de los objetos 
     * TODO: Use Enum DSE for good practices
     * TODO: CANTIDAD_DE_OBJS_EXISTENTES = Objetos.values().length
     */
    public static final int CANTIDAD_DE_OBJS_EXISTENTES = 7; // cantidad de objetos cuadrado mas 6 circulos
    public static final int EMPTY_SLOT = -1; // Cuadro vacio en el tablero
    public static final int CUADRADO = 0;
    public static final int BOLA_ROJA = 1;
    public static final int BOLA_AZUL = 2;
    public static final int BOLA_VERDE = 3;
    public static final int BOLA_NARANJA = 4;
    public static final int BOLA_MAGENTA = 5;
    public static final int BOLA_AMARILLA = 6;

    /**
     * Object colors in order of the objects indexes representation
     */
    public static final Colores[] colors = new Colores[]{
        Colores.WHITE,
        Colores.RED,
        Colores.GREEN,
        Colores.BLUE,
        Colores.YELLOW,
        Colores.ORANGE,
        Colores.MAGENTA,
    };

	/**
	 * Jugada valida:
	 * JUGADA_OBJ_A_MOVER_FILA: representa la fila del objeto a mover
     * JUGADA_OBJ_A_MOVER_COL: representa la columna del objeto a mover
     * JUGADA_LUGAR_A_MOVER_FILA: representa la fila del cuadro a donde se va a mover
     * JUGADA_LUGAR_A_MOVER_COL: representa la fila del cuadro a donde se va a mover
	 */
	public static final int JUGADA_OBJ_A_MOVER_FILA = 0;
	public static final int JUGADA_OBJ_A_MOVER_COL = 1;
	public static final int JUGADA_LUGAR_A_MOVER_FILA = 2;
	public static final int JUGADA_LUGAR_A_MOVER_COL = 3;
	public static int[] jugada = new int[4];

    /**
     * contador_de_objetos: Representa la cantidad de cada objeto en el
     * tablero, y el indice corresponde al valor del objeto representado en
     * las constantes.
     * 
     * DEFAULT_PROXIMOS_OBJETOS_CANTIDAD: Guarda la cantidad de objetos a
     * agregar por defecto.
     * 
     * proximosObjetos: guarda los proximos objetos a agregar en el tablero es
     * un array de enteros del 0 al DEFAULT_PROXIMOS_OBJETOS_CANTIDAD
     */
    public static int[] contador_de_objetos = {0, 0, 0, 0, 0, 0, 0};
    public static final int DEFAULT_PROXIMOS_OBJETOS_CANTIDAD = 3;
    public static int[] proximosObjetos = new int[DEFAULT_PROXIMOS_OBJETOS_CANTIDAD];

    /**
     * casillas: se almacenaran las casillas vacias seleccionadas de forma aleatorea.
     * FILA: indice para la fila en la estructura casilla
     * COLUMNA: indice para la columna en la estructura casilla
     *
     * Lo declaro aca para poder usarlo en la postcondicion.
     */
    public static final int FILA = 0; 
    public static final int COLUMNA = 1;
    public static int[][] casillas = new int[DEFAULT_PROXIMOS_OBJETOS_CANTIDAD][2];

    /**
     * Puntaje:
     * La varaible puntaje almacenara la cantidad de puntos acumulados al ir
     * alineando objetos.
     * Y las siguientes variables representan los puntos por cantidad de 
     * objetos alineados respectivamente
     */
    public static final int PUNTOS_POR_4 = 5;
    public static final int PUNTOS_POR_5 = 10;
    public static final int PUNTOS_POR_6 = 12;
    public static final int PUNTOS_POR_7 = 18;
    public static final int PUNTOS_POR_8_OR_MORE = 40;
    public static final int PUNTOS_POR_LESS_THAN_4 = 0;
	int puntaje = 0; // puntos acumulados por alineacion de objetos


    /*****************************************************************/
    /*************************** UTILITIES ***************************/
    /*****************************************************************/

    // Retorna un entero entre 0 y n es decir [0, n]
    /*@ requires 0 < n <= Integer.MAX_VALUE;
      @ ensures 0 <= \result <= n;
      @*/
    public static /*@ pure @*/ int getRandomInt(int n) {
        Random random = new Random();
        return random.nextInt(n + 1);
    }

    // Se suma el alto de la barra del titulo para normalizar el cuerpo del panel
    /**
     * Dado que cuando se abre, la ventana, el YMAX lo toma desde el inicio de la
     * ventana, no desde el punto (0,0), hay que sumarle la altura de la barra del
     * titulo al PANEL_YMAX para normalizar la altura del panel editable.
     */
    /*@ requires true;
      @ ensures \result == (PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA);
      @*/
    public static /*@ pure @*/ int normalizedPanelYMAX() {
        return PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA;
    }

    /**
     * Retorna el numero divisible por M mas cercano a N
     * @param N - un entero mayor o igual a M
     * @param M - un entero mayor a cero
     */ 
    /*@ requires 0 < N <= Integer.MAX_VALUE;
      @ requires 0 < M <=  Integer.MAX_VALUE;
      @ requires M <= N;
      @*/
    public static /*@ pure @*/ int NormalizeToExactlyDivisible(int N, int M) {
        int divisible = (int)Math.round(N / M) * M;
        return divisible;
    }

    /**
     * Dibuja una linea horizontal de largo l desde el punto (x,y) dado
     *
     * @param plt - el panel a dibujar
     * @param x - la coordenada x del punto de origen
     * @param y - la coordenada y del punto de origen
     * @param l - el largo deseado de la linea
     * @param color - el color de la linea
     */
    /*@ requires plt != null;
      @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires l < Integer.MAX_VALUE;
      @ requires color != null;
      @*/
    public static /*@ pure @*/ void dibujarLineaHorizontal(MaquinaDeTrazados plt, int x, int y, int l, Colores color) {
        plt.dibujarLinea(
            x, y,
            x + l, y,
            color
        );
        plt.mostrar();
    }

    /**
     * Dibuja una linea vertical de largo l desde el punto (x,y) dado
     *
     * @param plt - el panel a dibujar
     * @param x - la coordenada x del punto de origen
     * @param y - la coordenada y del punto de origen
     * @param l - el largo deseado de la linea
     * @param color - el color de la linea
     */
    /*@ requires plt != null;
      @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires l < Integer.MAX_VALUE;
      @ requires color != null;
      @*/
    public static /*@ pure @*/ void dibujarLineaVertical(MaquinaDeTrazados plt, int x, int y, int l, Colores color) {
        plt.dibujarLinea(
            x, y,
            x, y + l,
            color
        );
        plt.mostrar();
    }

    /**
     * Dibuja los indices del tablero
     */
    /*@ requires plt != null;
      @ requires 0 <= x <= PANEL_XMAX;
      @ requires 0 <= y <= PANEL_YMAX;
      @ requires 0 < size < Integer.MAX_VALUE;
      @ requires 0 < slots_number < Integer.MAX_VALUE;
      @*/
    public static /*@ pure @*/ void dibujarIndices(MaquinaDeTrazados plt, int x, int y, int size, int slots_number) {
        int i = 0;
        int LINE_WIDTH = 1;
        int SLOT_WIDTH = size / slots_number;

        if (PANEL_XMAX <= 350)
            plt.configurarFuente("SansSerif", Font.PLAIN, 8);

        /*@ maintaining 0 <= i <= slots_number;
          @ maintaining true;
          @ decreasing slots_number - i;
          @*/
		while(i < slots_number) {
            // Numero horizontal del slot
            plt.dibujarString(
                Integer.toString(i),
                x + SLOT_WIDTH * i + (SLOT_WIDTH / 2) - ANCHO_FUENTE,
                y - (SLOT_WIDTH / 2) + ALTO_FUENTE
            );
            
            // Pintar numero vertical
            plt.dibujarString(
                Integer.toString(i),
                x - (SLOT_WIDTH / 2),
                y + SLOT_WIDTH * i + (SLOT_WIDTH / 2) + ALTO_FUENTE
            );
            i++;
		}
	}

    /**
     * Dibuja la cuadrilla del tablero
     */
    /*@ requires plt != null;
      @ requires 0 <= x <= PANEL_XMAX;
      @ requires 0 <= y <= PANEL_YMAX;
      @ requires 0 < size < Integer.MAX_VALUE;
      @ requires 0 < slots_number < Integer.MAX_VALUE;
      @*/
	public static /*@ pure @*/ void dibujarCuadrilla(MaquinaDeTrazados plt, int x, int y, int size, int slots_number) {
        int i = 0;
        int LINE_WIDTH = 1;
        int SLOT_WIDTH = size / slots_number;

		while(i < slots_number + 1) {
            // Linea Horizontal del grid
			dibujarLineaHorizontal(plt, x, y + SLOT_WIDTH * i, size, Colores.BLACK);
            // Linea Vertical del grid
			dibujarLineaVertical(plt, x + SLOT_WIDTH * i, y, size, Colores.BLACK);
            i++;
		}
	}

    /**
     * Pinta el tipo de elemento con centro en (x,y)
     * 
     * @param plt - panel a pintar
     * @param x - coordenada x del centro del elemento
     * @param columna - coordenada y del centro del elemento
     * @param elemento - indice del elemento en la representacion de objetos
     */
    /*@ requires plt != null;
      @ requires 0 <= x <= PANEL_DEFAULT_XMAX;
      @ requires 0 <= y <= PANEL_DEFAULT_YMAX;
      @ requires 0 <= elemento <= 6;
      @*/
    public static /*@ pure @*/ void dibujarElemento(MaquinaDeTrazados plt, int x, int y, int elemento) {
        int SLOT_WIDTH = TABLERO_SIZE / TABLERO_SLOTS;

        if (elemento == CUADRADO) {
            DibujosVarios.dibujarCuadradoLleno(
                plt, x, y,
                SLOT_WIDTH,
                colors[CUADRADO]
            );
            return;
        }

        DibujosVarios.dibujarCirculoLleno(
            plt, x, y,
            SLOT_WIDTH / 2,
            colors[elemento]
        );
    }

    /**
     * Asigna las coordenadas del objeto en el centro de la casilla 
     * correspondiente en el array coords.
     * @param fila - fila del elemento en el tablero
     * @param columna - columna del elemento en el tablero
     * @param coords - el array de tamaño 2 donde se guardaran las coordenadas
     * del objeto en el tablero.
     */
    /*@ requires coords != null;
      @ requires 0 <= fila <= PANEL_DEFAULT_XMAX;
      @ requires 0 <= columna <= PANEL_DEFAULT_YMAX;
      @*/
    public static /*@ pure @*/ void obtenerCoordenadasDeElementoEnTablero(int fila, int columna, int[] coords) {
        int SLOT_WIDTH = TABLERO_SIZE / TABLERO_SLOTS;

        // desplaza en x desde TABLERO_X_POS el tamaño del slot 1.5 filas, es decir en la mitad de la fila correspondiente
        int SLOT_CENTER_FILA = TABLERO_Y_POS + fila * SLOT_WIDTH + (int)Math.round(SLOT_WIDTH / 2);
        // desplaza en y desde TABLERO_Y_POS el tamaño del slot 1.5 columnas, es decir en la mitad de la columna correspondiente
        int SLOT_CENTER_COLUMNA = TABLERO_X_POS + columna * SLOT_WIDTH + (int)Math.round(SLOT_WIDTH / 2);

        coords[0] = SLOT_CENTER_COLUMNA;
        coords[1] = SLOT_CENTER_FILA;
    }

    /**
     * Dibuja los elementos en el tablero
     */
    /*@ requires panel != null;
      @ requires tablero != null;
      @*/
    public static /*@ pure @*/ void dibujarElementosEnElTablero(MaquinaDeTrazados panel) {
        int fila = 0, X = 0, Y = 1, columna;
        int [] coords = new int[2];

        /*@ maintaining 0 <= fila <= tablero.length; 
          @ maintaining true;
          @ decreasing tablero.length - fila;
          @*/
        while(fila < tablero.length) {
            columna = 0;

            /*@ maintaining 0 <= columna <= tablero.length;
              @ maintaining true;
              @ decreasing tablero.length - columna;
              @*/
            while(columna < tablero[fila].length) {
                obtenerCoordenadasDeElementoEnTablero(fila, columna, coords);
                if (tablero[fila][columna] != EMPTY_SLOT)
                    dibujarElemento(panel, coords[X], coords[Y], tablero[fila][columna]);
                
                columna++;
            }
            fila++;
        }
    }

    /**
     * Dibuja el tablero de juego en el panel
     */
    /*@ requires panel != null;
      @ requires tablero != null;
      @*/
    public static /*@ pure @*/ void dibujarTablero(MaquinaDeTrazados panel) {
        int SLOT_SIZE;
        int MARGEN_Y = (int)Math.round(PANEL_YMAX * 0.05); // 5% de margen vertical

        TABLERO_SIZE = NormalizeToExactlyDivisible(
            (int)Math.round(Math.min(PANEL_XMAX, PANEL_YMAX) * 0.7),
            DEFAULT_TABLERO_SLOTS
        );

        SLOT_SIZE = TABLERO_SIZE / DEFAULT_TABLERO_SLOTS;

        /**
         * TABLERO_X_POS: Al tamaño del tablero se le agrega el tamaño de un
         * Slot (El tamaño donde ira el numero del indice) y se centra.
         * TABLERO_Y_POS: se coloca el tablero a MARGEN_Y de la parte inferior
         * del panel.
         */
        TABLERO_X_POS = PANEL_XMAX / 2 - (TABLERO_SIZE - SLOT_SIZE / 2) / 2;
        TABLERO_Y_POS = PANEL_YMAX - TABLERO_SIZE - MARGEN_Y;

        dibujarCuadrilla(panel, TABLERO_X_POS, TABLERO_Y_POS, TABLERO_SIZE, DEFAULT_TABLERO_SLOTS);
        dibujarIndices(panel, TABLERO_X_POS, TABLERO_Y_POS, TABLERO_SIZE, DEFAULT_TABLERO_SLOTS);
        dibujarElementosEnElTablero(panel);
    }

    /********************************************************************/
    /************************* LOGICA DEL JUEGO *************************/
    /********************************************************************/

    /**
     * Retorna el objeto en menor cantidad el el objeto. En este caso el indice
     * corresponde al valor que representa el objeto
     *
     * @return int
     */
    /*@ requires contador_de_objetos != null;
      @ requires (\forall int i; 0 <= i && i < contador_de_objetos.length; 0 <= contador_de_objetos[i] <= Integer.MAX_VALUE);
      @ ensures (\forall int i; 0 <= i && i < contador_de_objetos.length; contador_de_objetos[\result] <= contador_de_objetos[i]);
      @*/
    public static /*@ pure @*/ int obtenerObjEnMenorCantidad() {
        int i = 1, menor = 0;

        while (i < contador_de_objetos.length) {
            if (contador_de_objetos[i] < contador_de_objetos[menor])
                menor = i;
            i++;
        }

        return menor;
    }

    /**
     * Procedimiento 2: Obtiene los proximos elementos a agregar y los guarda
     * en proximosObjetos. Los dos primeros son random, y el ultimo es el que
     * se encuentra en menor cantidad en el tablero.
     */
    /*@ requires proximosObjetos != null;
      @ ensures \forall int i; 0 <= i && i < proximosObjetos.length; 0 <= proximosObjetos[i] && proximosObjetos[i] < CANTIDAD_DE_OBJS_EXISTENTES;
      @*/
    public static /*@ pure @*/ void obtenerProximosObjetos() {
        int i = 0, n = proximosObjetos.length;
        while(i < n - 1) {
            proximosObjetos[0] = getRandomInt(CANTIDAD_DE_OBJS_EXISTENTES - 1);  // -1 porque retorna [0, n]

            i++;
        }
        proximosObjetos[n -1] = obtenerObjEnMenorCantidad();
    }

    /**
     * Retorna simplemente si la casilla está marcada como vacia es decir si
     * el valor es EMPTY_SLOT (-1)
     *
     * @param fila valor de la fila de la casilla
     * @param columna valor de la columna de la casilla
     * @return (boolean) retorna si la casilla esta vacia
     */
    /*@ requires tablero != null;
      @ requires 0 <= fila < DEFAULT_TABLERO_SLOTS;
      @ requires 0 <= columna < DEFAULT_TABLERO_SLOTS;
      @ ensures \result <==> tablero[fila][columna] == EMPTY_SLOT;
      @*/
    public static /*@ pure @*/ boolean esCasillaVacia(int fila, int columna) {
        return tablero[fila][columna] == EMPTY_SLOT;
    }

    /**
     * Asigna la fila y la columna de una casilla vacia de manera aleatoria
     * 
     * TODO: improve algorithm performance by adding a global counter with the
     * TODO: empty slots amount and getting all this slots in an array of this
     * TODO: counter size and returning a random index of this array
     * * Este refactor del counter se puede hacer sumando los objetos presentes
     * * en el tablero es decir sumar el array los valores del array
     * * contador_de_objetos y restandoselo al total de slots DEFAULT_TABLERO_SLOTS x DEFAULT_TABLERO_SLOTS
     */
    /*@ requires casilla != null;
      @ ensures 0 <= casilla[FILA] < DEFAULT_TABLERO_SLOTS;
      @ ensures 0 <= casilla[COLUMNA] < DEFAULT_TABLERO_SLOTS;
      @ ensures esCasillaVacia(casilla[FILA], casilla[COLUMNA]);
      @*/
    public static /*@ pure @*/ void obtenerCasillaRandomVacia(int[] casilla) {
        /**
         * Tecnica de elmininacion de un predicado de una conjunción
         * Cota: no hay una cota exacta, al ser numeros random depende de la aleatoriedad para conseguir la casilla vacia.
         */
        /*@ maintaining 0 <= casilla[FILA] < DEFAULT_TABLERO_SLOTS;
          @ maintaining 0 <= casilla[COLUMNA] < DEFAULT_TABLERO_SLOTS;
          @*/
        do {
            casilla[FILA] = getRandomInt(DEFAULT_TABLERO_SLOTS - 1);  // -1 porque retorna [0, n]
            casilla[COLUMNA] = getRandomInt(DEFAULT_TABLERO_SLOTS - 1);  // -1 porque retorna [0, n]
        } while (!esCasillaVacia(casilla[FILA], casilla[COLUMNA]));
    }

    /**
     * Aumenta la cantidad de un objeto en el tablero
     * @param objeto - valor representativo del objeto en las estructuras de array
     * @param cantidad - cantidad a aumentar en el array contador_de_objetos
     */
    /*@ requires 0 <= objeto <= CANTIDAD_DE_OBJS_EXISTENTES;
      @ requires 0 < cantidad <= DEFAULT_TABLERO_SLOTS*DEFAULT_TABLERO_SLOTS;
      @ ensures contador_de_objetos[objeto] == (\sum int i; 0 <= i && i < DEFAULT_TABLERO_SLOTS; (\num_of int j; 0 <= j && j < DEFAULT_TABLERO_SLOTS; tablero[i][j] == objeto));
      @*/
    public static /*@ pure @*/ void aumentarCantidadDeObjeto(int objeto, int cantidad) {
        contador_de_objetos[objeto] += cantidad;
    }

    /**
     * Agrega los proximos objetos en casillas vacias en el tablero
     * seleccionadas de manera aleatorea. 
     */
    /*@ requires tablero != null;
      @ requires proximosObjetos != null;
      @ requires (\forall int i; 0 <= i && i < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD; 0 <= proximosObjetos[i] && proximosObjetos[i] < CANTIDAD_DE_OBJS_EXISTENTES);
      @ ensures (\forall int k; 0 <= k && k < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD; tablero[casillas[k][FILA]][casillas[k][COLUMNA]] == proximosObjetos[k]);
      @*/
    public static /*@ pure @*/ void agregarProximosObjetos() {
        int i = 0;

        /*@ maintaining 0 <= i <= DEFAULT_PROXIMOS_OBJETOS_CANTIDAD;
          @ maintaining (\forall int k; 0 <= k && k < i; tablero[casillas[k][FILA]][casillas[k][COLUMNA]] == proximosObjetos[k]);
          @ decreasing DEFAULT_PROXIMOS_OBJETOS_CANTIDAD - i;
          @*/
        while (i < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD) {
            obtenerCasillaRandomVacia(casillas[i]);
            // Colocar el objeto en la casilla vacia al azar en la posicion i de las casillas 
            tablero[casillas[i][FILA]][casillas[i][COLUMNA]] = proximosObjetos[i];
            // aumentar la cantidad del objeto que agrega en el tablero
            aumentarCantidadDeObjeto(proximosObjetos[i], 1);

            i++;
        }
    }

    /**
     * Procedimiento 1: inicializa el tablero colocando los espacios vacios y
     * los 3 primeros objetos
     *
     * * En la postcondicion se evalua que se hayan agregado la cantidad inicial
     * * de objetos que por defecto es DEFAULT_PROXIMOS_OBJETOS_CANTIDAD.
     */
    /*@ requires tablero != null;
      @ requires proximosObjetos != null;
      @ ensures DEFAULT_PROXIMOS_OBJETOS_CANTIDAD == (\sum int i; 0 <= i && i < DEFAULT_TABLERO_SLOTS; (\num_of int j; 0 <= j && j < DEFAULT_TABLERO_SLOTS; tablero[i][j] != EMPTY_SLOT));
      @*/
	public static /*@ pure @*/ void inicializarTablero() {
        int fila = 0, columna;

        /*@ maintaining 0 <= fila <= DEFAULT_TABLERO_SLOTS;
          @ decreasing DEFAULT_TABLERO_SLOTS - fila;
          @*/
        while (fila < DEFAULT_TABLERO_SLOTS) {
            columna = 0;

            /*@ maintaining 0 <= columna <= DEFAULT_TABLERO_SLOTS;
              @ maintaining (\forall int i; 0 <= i && i < fila; (\forall int j; 0 <= j && j < columna; tablero[i][j] == EMPTY_SLOT));
              @ decreasing DEFAULT_TABLERO_SLOTS - columna;
              @*/
            while (columna < DEFAULT_TABLERO_SLOTS) {
                tablero[fila][columna] = EMPTY_SLOT;
                columna++;
            }
            fila++;
        }
        obtenerProximosObjetos();
        agregarProximosObjetos();
    }

    /**
     * Dibuja los proximos objetos a agregar
     */
    //@ requires plt != null;
    public static /*@ pure @*/ void dibujarProximosObjetos(MaquinaDeTrazados plt) {
        int i = 0;
        int SLOT_WIDTH = TABLERO_SIZE / TABLERO_SLOTS;
        int MARGEN_Y = (int)Math.round(PANEL_YMAX * 0.10); // 5% de margen vertical
        plt.dibujarString("Próximos:", TABLERO_X_POS - SLOT_WIDTH, MARGEN_Y + SLOT_WIDTH / 2);

        int positionFontAncho = 0;

        /*@ maintaining 0 <= i <= proximosObjetos.length;
          @ maintaining true;
          @ decreasing proximosObjetos.length - i;
          @*/
        while (i < proximosObjetos.length) {
            positionFontAncho = TABLERO_X_POS + (int)Math.round(SLOT_WIDTH * 1.5) * (i + 1);
            dibujarElemento(plt, positionFontAncho, MARGEN_Y + SLOT_WIDTH / 2 - ALTO_FUENTE, proximosObjetos[i]);

            i++;
        }
    }

    /**
     * Dibuja el puntaje
     */
    //@ requires plt != null;
    public static /*@ pure @*/ void dibujarPuntaje(MaquinaDeTrazados plt) {
        int SLOT_WIDTH = TABLERO_SIZE / TABLERO_SLOTS;
        int MARGEN_Y = (int)Math.round(PANEL_YMAX * 0.10); // 5% de margen vertical
        plt.dibujarString("Puntaje: " + 0, PANEL_XMAX - (int)Math.round(TABLERO_X_POS * 1.5), MARGEN_Y + SLOT_WIDTH / 2);
    }

    /**
     * Procedimiento 3: 
     */
	public static /*@ pure @*/ void mostrarJuego(MaquinaDeTrazados panel) {
        panel.limpiar();
        dibujarTablero(panel);
        dibujarProximosObjetos(panel);
        dibujarPuntaje(panel);
        panel.repintar();
    }

    /*@ requires tablero != null;
      @ requires 0 <= fila < tablero.length;
      @ requires 0 <= columna < tablero.length;
      @*/
    public static /*@ pure @*/ boolean sePuedeMover(int fila, int columna) {
        int i = fila - 1;
        int j;
        
        /*@ maintaining fila - 1 <= i <= fila + 2;
          @ decreasing fila + 1 - i;
          @*/
        while (i <= fila + 1) {
            j = columna - 1;

            /*@ maintaining columna - 1 <= j <= columna + 2;
              @ decreasing columna + 1 - j;
              @*/
            while (j <= columna + 1) {
                // Excluir el objeto seleccionado
                if (i == fila && j == columna) {
                    j++;
                    continue;
                }

                // Comprobar indices dentro de rango (avoid out of bounds)
                if (i >= 0 && i < tablero.length && j >= 0 && j < tablero.length) {
                    if (tablero[i][j] == EMPTY_SLOT) return true;
                }

                j++;
            }
            i++;
        }

        return false;
    }

    /**
     * Procedimiento 4: obtiene una jugada por consola y verifica si es valida
     */
	public static /*@ pure @*/ void obtenerJugadaValida() {
        boolean jugadaInvalida = false, casillaInvalida = false;

        do {
            // Utils.cleanConsole();
            if (casillaInvalida)
                System.out.println("La casilla está vacia. Debe seleccionar un objeto!\n");

            if(jugadaInvalida) {
                System.out.println("El objeto no puede ser movido");
                System.out.println("Debe tener al menos una casilla vacia a su alrededor.");
                System.out.println("Por favor introduzca un objeto con al menos una casilla libre a su alrrededor.\n");
            }
              
            System.out.println("Introduzca la fila y la columna del objeto que desea mover separados por un espacio.\n");
            System.out.print("FILA COLUMNA: ");
            jugada[JUGADA_OBJ_A_MOVER_FILA] = consola.nextInt();
            jugada[JUGADA_OBJ_A_MOVER_COL] = consola.nextInt();

            casillaInvalida = esCasillaVacia(
                jugada[JUGADA_OBJ_A_MOVER_FILA],
                jugada[JUGADA_OBJ_A_MOVER_COL]
            );

            jugadaInvalida = !sePuedeMover(
                jugada[JUGADA_OBJ_A_MOVER_FILA],
                jugada[JUGADA_OBJ_A_MOVER_COL]
            );
        } while (jugadaInvalida || casillaInvalida);

        jugadaInvalida = false;

        do {
            // Utils.cleanConsole();
            if(jugadaInvalida)
                System.out.println("La casilla debe estar vacia");
                System.out.println("Por favor introduzca una casilla libre.\n");

            System.out.println("Introduzca la fila y la columna de la casilla a la que desea mover el objeto separados por espacio\n");

            System.out.print("FILA COLUMNA: ");
            jugada[JUGADA_LUGAR_A_MOVER_FILA] = consola.nextInt();
            jugada[JUGADA_LUGAR_A_MOVER_COL] = consola.nextInt();

            jugadaInvalida = !esCasillaVacia(
                jugada[JUGADA_LUGAR_A_MOVER_FILA],
                jugada[JUGADA_LUGAR_A_MOVER_COL]
            );
        } while (jugadaInvalida);
    }

    /**
     * Procedimiento 5: realizar la jugada obtenida moviendo el objeto en la
     * posicion (jugada[JUGADA_OBJ_A_MOVER_FILA], jugada[JUGADA_OBJ_A_MOVER_COL])
     * a la posicion (jugada[JUGADA_LUGAR_A_MOVER_FILA], jugada[JUGADA_LUGAR_A_MOVER_COL])
     */
	public static /*@ pure @*/ void moverObjetoSeleccionado() {
        // mover el objeto
        tablero[
            jugada[JUGADA_LUGAR_A_MOVER_FILA]
        ][
            jugada[JUGADA_LUGAR_A_MOVER_COL]
        ] = tablero[
            jugada[JUGADA_OBJ_A_MOVER_FILA]
        ][
            jugada[JUGADA_OBJ_A_MOVER_COL]
        ];

        // Vaciar lugar donde estaba el objeto
        tablero[
            jugada[JUGADA_OBJ_A_MOVER_FILA]
        ][
            jugada[JUGADA_OBJ_A_MOVER_COL]
        ] = EMPTY_SLOT;
    }

    /**
     * Función 2: Determina si es fin de juego restando la suma de los objetos
     * existentes en el tablero .
     */
	public static /*@ pure @*/ boolean esFinDeJuego() {
        int i = 0, suma = 0;
        for(i = 0; i < contador_de_objetos.length; i++) {
            suma += contador_de_objetos[i];
        }

        return suma == TABLERO_SLOTS*TABLERO_SLOTS;
    }

    public static void procesarFinalDeJuego(MaquinaDeTrazados panel) {
        panel.terminar();

        System.out.println("\n\tEL JUEGO HA FINALIZADO\n");
        System.out.println("\tGracias por jugar!");
        System.out.println("\tPronto lanzaremos una release con nuevas features y fixes");
        System.out.println("\tEstad atentos! :)");

        System.out.println(PANEL_DEFAULT_TITLE);
    }

    public static void iniciarJuego() {
        MaquinaDeTrazados panel = new MaquinaDeTrazados(
            PANEL_XMAX,
            normalizedPanelYMAX(),
            PANEL_DEFAULT_TITLE,
            Colores.LIGHT_GRAY
        );

        System.out.println("\n\t\tBIENVENIDO EL JUEGO HA INICIADO\n");
        
        // Utils.cleanConsole();
        inicializarTablero();
        obtenerProximosObjetos();
        while (!esFinDeJuego()) {
            // Mostrar-Estado-del-Juego;
            mostrarJuego(panel);
            // Utils.imprimirTableroPorConsola(tablero, 9);

            // Obtener-Jugada-Valida;
            obtenerJugadaValida();

            // Mover-Objeto-Seleccionado;
            moverObjetoSeleccionado();

            // Mostrar-Estado-del-Juego; (ACTUALIZAR)
            mostrarJuego(panel);
            // Utils.imprimirTableroPorConsola(tablero, 9);

            // Agregar-Proximos-Objetos;
            agregarProximosObjetos();

            // Obtener-Proximos-Objetos;
            obtenerProximosObjetos();

            // Mostrar-Estado-del-Juego; (ACTUALIZAR)
            mostrarJuego(panel);
        }

        // Procesar-Final-Juego;
        procesarFinalDeJuego(panel);
    }

    public static void main(String[] args) {
        iniciarJuego();
        /**
         * Next release (V 1.1.Alfa):
         * 
         * * Features:
         *      Eliminar patrones y Acumular puntos
         *      Leer-Configuracion-Desde-Los-Args;
         *      Iprimir-menu-Del-Juego;
         *           1.- Iniciar Juego
         *           2.- Leer Reglas del Juego
         *           3.- Configuración
         *               - Aumentar tamaño del tablero
         *               - Configurar Tamaño del panel
         *               - Normalizar Altura del panel
         *               - Cantidad de proximos objetos a agregar
         *               - Aumentar dificultad
         *                   - Mostrar el panel solo por unos segundos
         *                   - Aumentar el numero de alineaciones
         *                   - Aumentar Cantidad de proximos Objetos a agregar
         * 
         * ? Note: hasta ahora el responsive solo se puede cambiar
         * ? modificando las constantes PANEL_YMAX y PANEL_XMAX. Se ve bastante
         * ? bien desde 250x250 en adelante (Por defecto es 512x512)
         * 
         * ! Fixes:
         *      Agregar el jml restante
         *      Optimizar algoritmos de casilla random
         */
    }
}