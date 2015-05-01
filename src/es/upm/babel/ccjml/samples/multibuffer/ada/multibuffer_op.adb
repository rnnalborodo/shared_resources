--  Solución para el problema del multibuffer con requeue (con vivacidad)

--  COMENTARIO: Las peticiones de poner (o tomar) se atienden en
--  estricto orden de llegada (política equitativa).

--  with Ada.Text_Io;
--  use Ada.Text_Io;

with Conc_IO;
use Conc_IO;

with Ada.Numerics.Discrete_Random;

procedure Multibuffer_Op is

   subtype Item_Type is Natural;

   Num_Consumers : constant Positive := 8;
   Num_Producers : constant Positive := 4;


   --  The bounded buffer is a protected object with synchronization

   --  Constants and type definitions
   --  They cannot go into the object : only the state lives there!
   Buffer_Size : constant Natural := 10;

   --  A modular type gives a shorter and more readable code
   subtype Buffer_Quantity is Natural range 0 .. Buffer_Size;
   type Buffer_Range is mod Buffer_Size;

   --  The buffer itself in an array
   type Container_Array is array (Buffer_Range range <>) of Item_Type;

   --  random generation of amounts of items to get or to put
   --  The maximum number of data which can be added to/retrieved from the
   --  array is Buffer_Size/2, in order to avoid interlocking.
   subtype Random_Range is
     Buffer_Range range 1 .. Buffer_Range (Buffer_Size / 2);

   package Random_Amount is
      new Ada.Numerics.Discrete_Random (Random_Range);
   use Random_Amount;

   protected type MultiBuffer is
      entry Get (Items : out Container_Array);  --  We need synchronization
      entry Put (Items : in Container_Array);
   private
      --  State declaration
      Container : Container_Array (Buffer_Range);

      --  Number of items currently in the array
      Item_Counter : Buffer_Quantity := 0;
      Put_Pointer : Buffer_Range := Buffer_Range'First;
      Get_Pointer : Buffer_Range := Buffer_Range'First;

      --  Variables for the two-phase lock
      Delayed_Get : Boolean := False;
      Items_To_Get : Buffer_Quantity;
      Delayed_Put : Boolean := False;
      Items_To_Put : Buffer_Quantity;

      --  privated entries for second phase of the lock
      entry Delay_Get
        (Item : out Container_Array);
      entry Delay_Put
        (Item : in Container_Array);

      --  auxiliar procedures
      procedure Add
        (Item : in Container_Array);
      procedure Remove
        (Item : out Container_Array);
      procedure Insert
        (In_Data : in     Container_Array;
         Container : in out Container_Array;
         First_Out_Pos : in     Buffer_Range;
         First_In_Pos : in     Buffer_Range;
         Last_In_Pos : in     Buffer_Range);
   end MultiBuffer;

   protected body MultiBuffer
   is
      entry Get
        (Items : out Container_Array)
      when not Delayed_Get is
      begin
         --  Test precondition
         if not (Item_Counter >= Items'Length) then
            --  Save the relevant arguments as part of the resource state.
            --  This is actually not part of the resource itself as
            --  initially designed, but an artifact to remember later which
            --  calls were blocked.
            Items_To_Get := Items'Length;
            Delayed_Get := True;
            requeue Delay_Get;
         else --  Do it right now.
            Remove (Items);
         end if;
      end Get;


      entry Put
        (Items : in Container_Array)
      when not Delayed_Put is
      begin
         --  Test precondition.  As above.
         if not (Buffer_Size - Item_Counter >= Items'Length) then
            Items_To_Put := Items'Length;
            Delayed_Put := True;
            requeue Delay_Put;
         else
            Add (Items);
         end if;
      end Put;

      entry Delay_Get
        (Item : out Container_Array)
      when Items_To_Get <= Item_Counter is
      begin
         Delayed_Get := False;
         Remove (Item); --  Remove uses the previously saved state
      end Delay_Get;


      entry Delay_Put
        (Item : in Container_Array)
      when Items_To_Put <= Buffer_Size - Item_Counter is
      begin
         Delayed_Put := False;
         Add (Item);
      end Delay_Put;

      procedure Remove (Item : out Container_Array) is
      begin
         --  Take out the items needed by the caller
         Insert (Container,
                 Item (Item'First .. Item'Last),
                 Item'First,
                 Get_Pointer,
                 Get_Pointer + Item'Length-1);
         Get_Pointer := Get_Pointer + Item'Length;
         Item_Counter := Item_Counter - Item'Length;
      end Remove;

      procedure Add (Item : in Container_Array) is
      begin
         --  se añaden los datos (Item) al buffer
         Insert (Item (Item'First .. Item'Last),
                 Container,
                 Put_Pointer,
                 Item'First,
                 Item'Last);
         Put_Pointer := Put_Pointer + Item'Length;
         Item_Counter := Item_Counter + Item'Length;
      end Add;

      procedure Insert
        (In_Data : in     Container_Array;
         Container : in out Container_Array;
         First_Out_Pos : in     Buffer_Range;
         First_In_Pos : in     Buffer_Range;
         Last_In_Pos : in     Buffer_Range)
      is
         I : Buffer_Range := First_In_Pos;
         J : Buffer_Range := First_Out_Pos;
      begin
         while I /= Last_In_Pos + 1  loop
            Container (J) := In_Data (I);
            J := J + 1;
            I := I + 1;
         end loop;
      end Insert;

   end MultiBuffer;


   Pool : MultiBuffer;

   --  Each producer and consumer is a task

   task type Producer_Type;
   task body Producer_Type is
      Num : Random_Range;
      G : Generator;
      Items : constant Container_Array (Random_Range) := (others => 0);
   begin
      Reset (G);
      loop
         delay 2.0; --  Produce data (Item)
         Num := Random (G);
         Put_Line ("Producer generates " &
                   Random_Range'Image (Num) &
                   " items");
         Pool.Put (Items (1 .. Num));
         Put_Line ("Producer puts " &
                   Random_Range'Image (Num) &
                   " items");
      end loop;
   end Producer_Type;


   task type Consumer_Type;
   task body Consumer_Type is
      Num : Random_Range;
      G : Generator;
      Items : Container_Array (Random_Range);
   begin
      Reset (G);
      loop
         Num := Random (G);
         Put_Line ("Consumer wants " & Random_Range'Image (Num) & " items");
         Pool.Get (Items (1 .. Num));
         Put_Line ("Consumer gets " & Random_Range'Image (Num) & " items");
         delay 2.0; --  está consumiendo los datos (Item)
      end loop;

   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers : array (1 .. Num_Consumers) of Consumer_Type;
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Multibuffer_Op;

