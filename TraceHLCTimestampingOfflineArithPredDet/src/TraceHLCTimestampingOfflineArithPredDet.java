import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.Locator;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import com.microsoft.z3.*;
import java.nio.file.*;
public class TraceHLCTimestampingOfflineArithPredDet {
    static int snapshotcount=0;
    static int flex_window_snapshotcount=0;
    static int fixed_window_snapshotcount=0;
    static int smtBasedSnapshotCount=0;
    static String inpfilename="";
    static int debugmode=0;
    static int msgmode=0; //msg distribution mode
    static String clockmode="HLC";
    static float gamma = 0;//value by which right end point of the interval will be extended
	static int intervDropFreq=0;
    static int msgDropFreq=0;
    static String outputLocation = "";
    static String backslash="\\";
    static boolean HLCplusEpsPlusSMT;
    static int batchlength=0;
    public static void main(String[] args) {
        try {
            if(args.length < 5) {
                System.out.println("Expected number of arguments: 5. Provided "+args.length);
                System.exit(0);
            }
            debugmode = Integer.parseInt(args[0]); //debugmode==1 is printing mode, debugmode == 2 only prints changepoints and candidates
            msgmode=Integer.parseInt(args[1]); //if 2-different-msg-distr-mode, anything else is normal msg distribution mode..
            //setting gamma
            gamma = Float.parseFloat(args[2]);
            intervDropFreq = Integer.parseInt(args[3]);
            msgDropFreq = Integer.parseInt(args[4]);
            inpfilename = args[5];
            outputLocation = args[6];
            batchlength=100;
            HLCplusEpsPlusSMT=true;
            File inputFile = new File(inpfilename);			
			if(System.getProperty("os.name").toLowerCase().indexOf("win") >= 0){
				backslash="\\";
			} else {
				backslash="/";
			}
            SAXParserFactory factory = SAXParserFactory.newInstance();
            SAXParser saxParser = factory.newSAXParser();//create XML parser instance
            UserHandler userhandler = new UserHandler();
            saxParser.parse(inputFile, userhandler);
            System.out.println("The total snapshot count: "+snapshotcount);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
class UserHandler extends DefaultHandler
{
	private Locator locator;
	public void setDocumentLocator( Locator locator )
	{
	this.locator = locator;
	}
    boolean bmsender_time = false;
    boolean bmsgto = false;
    boolean bmsgfrom = false;
    boolean bmreceiver_time = false;
    boolean bstart_time=false;
    boolean bend_time=false;
    boolean bmisc=false;
    int proc_id=-1;//variable to remember process id
    int sender_time=-1;// variable to remember sender time for message RECEIVE
    int senderid=-1;// variable to remember sender id for message RECEIVE
    SysAtHand sysathand=new SysAtHand(); //object that accounts for epsilon and number of processes in current system
	String fromVtoEndStr = TraceHLCTimestampingOfflineArithPredDet.inpfilename.substring(TraceHLCTimestampingOfflineArithPredDet.inpfilename.indexOf("_v")+2, TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf(".xml"));
    String intervalLengthStr=fromVtoEndStr.substring(0, fromVtoEndStr.indexOf('_'));
    Map<Integer, Process> mapofprocesses = new HashMap<Integer, Process>();//map of processes with process id as the key and Process instance as value
    HLC largestIntervalEnd;
    //variables for printing z3 constraints for intervals
    String intervalConstraint="";
    int bracesCount=0;
    String folderName = TraceHLCTimestampingOfflineArithPredDet.inpfilename.substring(TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf('/')+1, TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf(".xml"));
    String nwfolder=TraceHLCTimestampingOfflineArithPredDet.outputLocation+TraceHLCTimestampingOfflineArithPredDet.backslash+folderName; //input file name without file extension
    int lastProcessedBatchPt=0, highestSeenCInBatch=0;
    Set<Integer> ProcsCrossedBatchEnd=new HashSet<Integer>();
    //variable for window based snapshot count for the overall run - including all batches if batch-wise execution was done
    HashSet<Integer> windowsSeen = new HashSet<Integer>();
    //variables for creating common smt constraints for all windows
    String commonConstraintsStr;
    HashSet<String> fileToProcessDuringNxtBatch=new HashSet<String>();//variable to remember file name corresponding to the last window in a batch
    boolean noMoreBatches=false;
    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException
    {
        if (qName.equalsIgnoreCase("message"))
        {
            String type = attributes.getValue("type");
            String process = attributes.getValue("process");
            //System.out.println("message " + type + " event at process " +process);
            proc_id=Integer.parseInt(process);
        }
        else if(qName.equalsIgnoreCase("sys"))
        {
            int eps = Integer.parseInt(attributes.getValue("epsilon"));
            int nproc = Integer.parseInt(attributes.getValue("number_of_processes"));
            //System.out.println("System: epsilon=" + eps + ", number_of_processes=" +nproc);
            sysathand.SetEpsilon(eps);
            sysathand.SetNumberOfProcesses(nproc);
            if(TraceHLCTimestampingOfflineArithPredDet.intervDropFreq!=0){
                sysathand.setInterval_length(Integer.parseInt(intervalLengthStr));
            }
            //setting gamma to epsilon if the provided value is positive
            if(TraceHLCTimestampingOfflineArithPredDet.gamma > 0){
                TraceHLCTimestampingOfflineArithPredDet.gamma = (int)Math.floor(sysathand.GetEpsilon() * TraceHLCTimestampingOfflineArithPredDet.gamma);
            } else {
                //use 0 as gamma value
            }
            //create nproc number of instances of class process and assign ids to them
            for (int i=0; i<nproc; i++){
                Clock nwclock=new Clock();
                if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC")){
                    Vector<Integer> hlcvector=new Vector<Integer>();
                    hlcvector.add(0);
                    hlcvector.add(0);
                    hlcvector.add(0);
                    nwclock=new HLC(hlcvector);
                }
                Process proc = new Process(i,nwclock);
                mapofprocesses.put(i,proc);
            }
            //variable to keep track of the largest know HLC timestamp -- needed to bound
            //epsilon extension of last change-points at processes
            Vector<Integer> tempVector = new Vector<Integer>();
            tempVector.add(0);
            tempVector.add(0);
            tempVector.add(0);
            largestIntervalEnd=new HLC(tempVector);
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                String vDeclarationStr="",lDeclarationStr="",epsilonConstraintsStr="",predicateConstraintsStr="(assert ";
                //Creating constraints common to all smt-constraint files
                for (int processId = 0; processId < sysathand.GetNumberOfProcesses(); processId++) {
                    //variable declaration constraints
                    //for each process declare a timestamp variable 'l' and local state variable 'x'
                    vDeclarationStr = vDeclarationStr + "(declare-const x_" + processId + " Bool)\n";
                    lDeclarationStr = lDeclarationStr + "(declare-const l" + processId + " Int)\n";
                    //epsilon constraints
                    for (int pr1 = 0; pr1 < sysathand.GetNumberOfProcesses(); pr1++) {
                        if (pr1 != processId) {
                            epsilonConstraintsStr = epsilonConstraintsStr + "(assert (or (and (< (- l" + processId + " l" + pr1 + ") " + sysathand.GetEpsilon() + ") (>= (- l" + processId + " l" + pr1 + ") 0)) (and (< (- l" + pr1 + " l" + processId + ") " + sysathand.GetEpsilon() + ") (>= (- l" + pr1 + " l" + processId + ") 0))))\n";
                        }
                    }
                    //violation/predicate constraints
                    if (processId != sysathand.GetNumberOfProcesses() - 1) {
                        predicateConstraintsStr = predicateConstraintsStr + "(and (= x_" + processId + " true) ";
                    } else {
                        predicateConstraintsStr = predicateConstraintsStr + "(= x_" + processId + " true)";
                    }
                }
                for (int pr = 0; pr < sysathand.GetNumberOfProcesses(); pr++) {
                    predicateConstraintsStr = predicateConstraintsStr + ")";
                }
                predicateConstraintsStr = predicateConstraintsStr + "\n";
                commonConstraintsStr = vDeclarationStr+lDeclarationStr+epsilonConstraintsStr+predicateConstraintsStr;
            }
        } else if (qName.equalsIgnoreCase("sender_time")) {
            bmsender_time = true;
        } else if (qName.equalsIgnoreCase("to")) {
            bmsgto = true;
        } else if (qName.equalsIgnoreCase("from")) {
            bmsgfrom = true;
        } else if (qName.equalsIgnoreCase("receiver_time")) {
            bmreceiver_time = true;
        } else if (qName.equalsIgnoreCase("interval")) {
            String process = attributes.getValue("process");
            //System.out.println("Interval at process " +process);
            proc_id=Integer.parseInt(process);
        } else if (qName.equalsIgnoreCase("start_time")) {
            bstart_time = true;
        } else if (qName.equalsIgnoreCase("end_time")) {
            bend_time = true;
        } else if (qName.equalsIgnoreCase("associated_variable")) {
            String name = attributes.getValue("name");
            String value = attributes.getValue("value");
            String old_value = attributes.getValue("old_value");
            Process proc= mapofprocesses.get(proc_id);
            //create separate version of clocks for the candidate
            Clock nwclock1, nwclock2;
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC")) {
                Vector<Integer> hlcvector1=new Vector<Integer>();
                hlcvector1.add(0);
                hlcvector1.add(0);
                hlcvector1.add(0);
                nwclock1=new HLC(hlcvector1);
                //there is guarantee that the old clock should correspond to
                //interval start because no event happens between intervals,
                //the interval start is either end of a false interval or
                //true interval (due to interval split due to communication),
                //either way this value is recorded as old clock value when
                //"endtime" of current interval got processed
                nwclock1.setClock(proc.getProcOldClock().getClock());
                Vector<Integer> hlcvector2=new Vector<Integer>();
                hlcvector2.add(0);
                hlcvector2.add(0);
                hlcvector2.add(0);
                nwclock2=new HLC(hlcvector2);
                nwclock2.setClock(proc.getProcClock().getClock());
                //keeping track of the actual clock value of the largest interval end
                if(largestIntervalEnd.lessThan(nwclock2)){
                    largestIntervalEnd.setClock(nwclock2.getClock());
                }
                nwclock2.setClockPlusValue((int)TraceHLCTimestampingOfflineArithPredDet.gamma);
                if(value.equals("true")) {
                    if(proc.getAcceptInterval()==0|| proc.getProcOldClock().getClock().elementAt(0)-proc.getLastAcceptedStartPt()< sysathand.getInterval_length()){
                        //this was used for an earlier implementation where intervals were
                        //reported as pairs of end-points and intervals during which the value of the local variable "x"
                        //at a process was true were also referred to as true-intervals were reported as "Candidates"
                        //add candidate to process queue
                        proc.newCandidateOccurance(nwclock1,nwclock2);
                        //add change-points to process-queues - current and next appropriately
                        //if right endpoint/changepoint is beyond the end of current batch
                        //and left endpoint/changepoint is within end of current batch
                        proc.newChangePoint(nwclock1,1,1);
                        proc.newChangePoint(nwclock2,-1,1);
                        proc.setLastAcceptedStartPt(proc.getProcOldClock().getClock().elementAt(0));//remember last accepted interval
                        proc.setAcceptInterval(TraceHLCTimestampingOfflineArithPredDet.intervDropFreq);
                    } else{
                        //counting ignored intervals - only if they are far from the previously ignored interval - Solution to interval splits due to communication issue
                        if(proc.getProcOldClock().getClock().elementAt(0)-proc.getLastIgnoredStartPt()> sysathand.getInterval_length()) {
                            proc.setAcceptInterval(proc.getAcceptInterval() - 1);
                            proc.setLastIgnoredStartPt(proc.getProcOldClock().getClock().elementAt(0));
                            //remember last ignored interval
                        }//if current interval is within interval_length of previously ignored interval then its not counted
                    }
                }/* //uncomment the else part below when you have the implementation for processing arithmetic intervals ready
                else{
                    proc.newChangePoint(nwclock1,1,0);
                    proc.newChangePoint(nwclock2,-1,0);
                }
                 */
                //write interval constraints to appropriate file irrespective of whether they are true or false intervals
                if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                    //create constraint
                    String variablename=""+name+"_"+proc_id+"";
                    //make sure to use the actual interval end-timestamps i.e. not the epsilon extended timestamps
                    intervalConstraint=intervalConstraint+"(assert (=> (and (<= "+proc.getProcOldClock().getClock().elementAt(0)+" l"+proc_id+") (< l"+ proc_id +" "+proc.getProcClock().getClock().elementAt(0)+")) (and (= "+variablename+" "+value+") ";
                    bracesCount++;
                    //System.out.println("End Element :" + qName+"\n");
                }
                mapofprocesses.put(proc_id,proc);
            }
        } else if (qName.equalsIgnoreCase("misc")) {
            bmisc = true;
        }
    }

    @Override
    public void endElement(String uri, String localName, String qName) throws SAXException
    {
        if (qName.equalsIgnoreCase("message")) {
            //System.out.println("End Element :" + qName+ "\n");
        } else if(qName.equalsIgnoreCase("associated_variable")) {
            //System.out.println("End Element :" + qName);
        } else if(qName.equalsIgnoreCase("misc")) {
            //System.out.println("End Element :" + qName);
        } else if(qName.equalsIgnoreCase("interval")) {
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                Process proc = mapofprocesses.get(proc_id);
                intervalConstraint = intervalConstraint + " true";
                while (bracesCount > 0) {
                    intervalConstraint = intervalConstraint + ")";
                    bracesCount--;
                }
                intervalConstraint = intervalConstraint + "))\n";
                //compute files/filenames to write to
                //window corresponding to left endpoint/changepoint - windows are defined based on physical time - because snapshots are counted based on physical-time-defined windows
                int lWindow = (proc.getProcOldClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                //window corresponding to right endpoint/changepoint
                int rWindow = (proc.getProcClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                HashSet<String> filesToWriteTo=new HashSet<String>();
                //for each window from lWindow to rWindow
                for (int windowStart = lWindow; windowStart <= rWindow; windowStart = windowStart + sysathand.GetEpsilon()) {
                    //compute the two files corresponding to the window
                    String file1Name, file2Name;
                    //write constraints to both files
                    //print z3 constraint
                    file1Name = "constraints_" + windowStart + "to" + (windowStart + (sysathand.GetEpsilon() * 2)) + ".smt2";
                    filesToWriteTo.add(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file1Name);
                    if (windowStart >= sysathand.GetEpsilon()) {
                        file2Name = "constraints_" + (windowStart - sysathand.GetEpsilon()) + "to" + (windowStart + sysathand.GetEpsilon()) + ".smt2";
                        filesToWriteTo.add(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file2Name);
                    }
                }
                //for each file in the hashset - write the interval constraint
                for (String fname: filesToWriteTo){
                    appendToFile(fname, intervalConstraint);
                }
                intervalConstraint = "";
                //System.out.println("End Element :" + qName+"\n");
                //Check if all processes reached the end of current batch - if yes invoke the chanepoints-processing-function
                if (lastProcessedBatchPt + TraceHLCTimestampingOfflineArithPredDet.batchlength + sysathand.GetEpsilon() < proc.getProcClock().getClock().elementAt(0)) {
                    ProcsCrossedBatchEnd.add(proc_id);
                    if (ProcsCrossedBatchEnd.size() == sysathand.number_of_processes) {
                        ProcessAndClearCandQueues_HLC();
                        ProcsCrossedBatchEnd.clear();
                        lastProcessedBatchPt = lastProcessedBatchPt + TraceHLCTimestampingOfflineArithPredDet.batchlength;
                        System.out.println("lastProcessedBatchPt:"+lastProcessedBatchPt+"\n");
                        highestSeenCInBatch = 0;
                    }
                }
                proc_id = -1;
            }
        } else if(qName.equalsIgnoreCase("system_run")) {
            //Since every batch is processed only when all processes cross batch-boundary = window end + epsilon(i.e.2* epsilon length) there is a pending window(of length epsilon) to be processed
            while(!noMoreBatches) { //noMoreBatches is set to true if at least process does not have any more changepoints to process
                ProcessAndClearCandQueues_HLC();
                ProcsCrossedBatchEnd.clear();
                lastProcessedBatchPt = lastProcessedBatchPt + TraceHLCTimestampingOfflineArithPredDet.batchlength;
                System.out.println("lastProcessedBatchPt:" + lastProcessedBatchPt + "\n");
                highestSeenCInBatch = 0;
            }
        }
    }
    @Override
    public void characters(char ch[], int start, int length) throws SAXException
    {
        if (bmsender_time) {
            sender_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Sender time: "+ sender_time);
            bmsender_time = false;
        } else if (bmsgto) {
            int msgto=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Message to: " + msgto);
            Process proc= mapofprocesses.get(proc_id);
            if(proc_id!=msgto) {
                proc.updateClockLocalOrSendMsg(sender_time,true);
            } else {
                proc.updateClockLocalOrSendMsg(sender_time,false);//no reporting required for intra-process communication, so logging corresponding l,c values in the queue is not required
            }
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT){
                //update highest seen C
                if(highestSeenCInBatch<proc.getProcClock().getClock().elementAt(2)) {
                    highestSeenCInBatch = proc.getProcClock().getClock().elementAt(2);
                }
            }
            mapofprocesses.put(proc_id,proc);
            proc_id=-1;
            sender_time=-1;
            //System.out.println("Clock updated after message send, l="+ proc.getL()+",c="+proc.getC());
            bmsgto = false;
        } else if (bmsgfrom) {
            senderid=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Message from: " +senderid );
            bmsgfrom = false;
        } else if (bmreceiver_time) {
            int receiver_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Receiver time: " + receiver_time);
            //get max of sendertime,receiver_time
            //update clock using that max
            Process proc= mapofprocesses.get(proc_id);
            boolean toss;
			if(TraceHLCTimestampingOfflineArithPredDet.msgmode==2){
                if(proc.getIgnoredMsgCnt()==0){
                    toss=true; //accept the message
                    proc.setIgnoredMsgCnt(TraceHLCTimestampingOfflineArithPredDet.msgDropFreq);
                } else {
                    toss=false; //ignore the message
                    proc.setIgnoredMsgCnt(proc.getIgnoredMsgCnt()-1);
                }
            } else {
                toss=true; // every process receives every message from any other process
            }
            if((proc_id!=senderid) && (toss)) {//based on senderid and on receiver-probability--- if in different msg distribution mode
                //get sender l,c by popping sender's dequeue
                Process senderproc= mapofprocesses.get(senderid);
                MessageSendStruct correspSendClk = senderproc.getClockfromQueue(sender_time);
                proc.updateClockMessageRceive(receiver_time, correspSendClk.getMsgClock());
                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
                if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                    String msgConstraint = ("(assert (=> (>= l" + proc_id + " " + proc.getProcClock().getClock().elementAt(0) + ") (not (<= l" + senderid + " " + correspSendClk.getMsgClock().getClock().elementAt(0) + "))))\n");
                    int windowStart = (proc.getProcClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                    String file1Name = "constraints_" + windowStart + "to" + (windowStart + (sysathand.GetEpsilon() * 2)) + ".smt2";
                    appendToFile(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file1Name, msgConstraint);
                    if (windowStart >= sysathand.GetEpsilon()) {
                        String file2Name = "constraints_" + (windowStart - sysathand.GetEpsilon()) + "to" + (windowStart + sysathand.GetEpsilon()) + ".smt2";
                        appendToFile(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file2Name, msgConstraint);
                    }
                }
            } else {
                if(proc_id!=senderid) { // case where it chose to ignore msg based on messgeacceptfrequency
                    // to pop corresponding sender info from its queue
                    Process senderproc= mapofprocesses.get(senderid);//get sender l,c by popping sender's dequeue
                    MessageSendStruct correspSendLC = senderproc.getClockfromQueue(sender_time);
                }
                proc.updateClockLocalOrSendMsg(receiver_time,false);
                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
            }
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                //update highest seen C
                if (highestSeenCInBatch < proc.getProcClock().getClock().elementAt(2)) {
                    highestSeenCInBatch = proc.getProcClock().getClock().elementAt(2);
                }
            }
            bmreceiver_time = false;
            proc_id=-1;
            sender_time=-1;
            senderid=-1;
        } else if (bstart_time) {
            //System.out.println("Interval start time: "+ new String(ch, start, length));
            bstart_time = false;
        } else if (bend_time) {
            int end_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Interval end time: " + end_time);
            Process proc= mapofprocesses.get(proc_id);
            //no need to update clocks if bmisc because the clock was already updated at message send/recieve which actually caused this interval end point
            //if(!bmisc)//some intervals marked as "splitduetocommunication" happen to exist in the traces - so update clock for all types of intervals
            {
                proc.updateClockLocalOrSendMsg(end_time,false);
                mapofprocesses.put(proc_id,proc);
            }
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                //update highest seen C
                if (highestSeenCInBatch < proc.getProcClock().getClock().elementAt(2)) {
                    highestSeenCInBatch = proc.getProcClock().getClock().elementAt(2);
                }
            }
            bmisc = false;
            bend_time = false;
        } else if (bmisc) {
            //System.out.println("misc: " + new String(ch, start, length));
        }
    }
    void ProcessAndClearCandQueues_HLC() {
        //variable for window based snapshot count within a batch
        HashSet<String> filesMarked = new HashSet<String>();
        System.out.println("Processing changepoint queue.");
        if (sysathand.GetNumberOfProcesses()==0) {
            System.out.println("Zero processes in system.");
            System.exit(0);
        }
        //get the text between last backslash and .xml
        String folderName = TraceHLCTimestampingOfflineArithPredDet.inpfilename.substring(TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf('/')+1, TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf(".xml"));
        String nwfolder=TraceHLCTimestampingOfflineArithPredDet.outputLocation+TraceHLCTimestampingOfflineArithPredDet.backslash+folderName; //input file name without file extension
        //For debugging purposes
        /*****************print all candidates and changepoints of all the processes before preprocessing***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
            String snapshot_cand_file="",snapshot_cpt_file="";
            if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
            } else {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        int strictBatchRt=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength;
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++){//loop through all process queues
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT){
                //any pair of changepoint with right changepoint-ohysical-timestamp greater than current window's strict right should be copied to next batch queue
                currProc.fillNextQueueFromCurrentQueue(strictBatchRt);
                if(currProc.getCPtQueueNextBatch().isEmpty()){
                    noMoreBatches=true;//last batch
                }
            }
            currProc.setCPtQueue(currProc.cleanUpChangePtQ());
            //currProc.fixLastChangepoint(largestIntervalEnd);
            //remember to update mapofprocesses accordingly
            mapofprocesses.put(i,currProc);
        }
        /*****************print all candidates and changepoints of all the processes to see if change points were processed correctly***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
            String snapshot_cand_file="",snapshot_cpt_file="";
            if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode +".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode +".txt";
            } else {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        //create variable overlap_count
        int overlap_count = 0;
        int prevtokenend = 0;
        int minCPtProc=-1;	//process corresponding to the minimum changepoint
        do { //until minCPtProc=-1 at the end of the loop - there is no more unprocessed changepoint to process
            /**********Find minimum among first changepoint in each process' queue*******/
            minCPtProc = findMinCptProc();
            //if at least one process had at least one changepoint to process, then minCPtProc is not -1
            if (minCPtProc!=-1)
            {
                //removing the minimum changepoint from the respective queue and processing it
                Process chosenProc= mapofprocesses.get(minCPtProc);//get the current state of the process
                Deque<ChangePoint> chosenProccPtq = chosenProc.getCPtQueue();//get the changepoint queue of the process
                if (chosenProccPtq.isEmpty()) {
                    System.out.println("Something went wrong. Queue at the chosen process is empty.");
                    System.exit(0);
                }
                ChangePoint currentCPt=chosenProccPtq.removeFirst();
                /**************************update overlap count accordingly**************************/
                overlap_count=overlap_count+currentCPt.getEndPointType();
                //remember the effect of clearing the candidate queue of the process
                chosenProc.setCPtQueue(chosenProccPtq);
                //remember to update mapofprocesses accordingly
                mapofprocesses.put(minCPtProc,chosenProc);
                /*************Report timestamp of overlap if it corresponds to a consistent cut****************/
                if (overlap_count==sysathand.GetNumberOfProcesses())
                {
                    String snapshot_outfile="",snapshot_flex_window_counted_outfile="",snapshot_fixed_window_counted_outfile="";
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                        //********************************creating needed files and folders reporting*******************************
                        if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                            snapshot_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_clk_"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                            snapshot_flex_window_counted_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_flex_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                            snapshot_fixed_window_counted_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_fixed_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                        } else {
                            snapshot_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_clk_"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                            snapshot_flex_window_counted_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_flex_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                            snapshot_fixed_window_counted_outfile=nwfolder+TraceHLCTimestampingOfflineArithPredDet.backslash+ "snapshots_fixed_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                        }
                        //Create folder and files only if it is the first time
                        if(TraceHLCTimestampingOfflineArithPredDet.snapshotcount==0){ //when the first cut gets detected clean the snapshots file if one already exists
                            fileClearCreateParentDirectory(snapshot_outfile);
                            fileClearCreateParentDirectory(snapshot_flex_window_counted_outfile);
                            fileClearCreateParentDirectory(snapshot_fixed_window_counted_outfile);
                        }
                    //}
                    boolean markifcounted=false;
                    /*********************FLEXIBLE WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    prevtokenend = flexWindowCountSnapshot(currentCPt, prevtokenend,minCPtProc,snapshot_flex_window_counted_outfile);
                    /*********************FIXED WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    if (fixedWindowCountSnapshot(currentCPt,windowsSeen,minCPtProc,snapshot_fixed_window_counted_outfile)){//if snapshot was counted as new
                        markifcounted = true;
                        if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                            //mark the smt constraint file for the corresponding window if the snapshot was counted as new
                            //identify corresponding file name
                            int windowStart = (currentCPt.getcPointTimestamp().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                            //add filename-string to a set-of-strings for the current batch
                            String file1Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "constraints_" + windowStart + "to" + (windowStart + (sysathand.GetEpsilon() * 2)) + ".smt2";
                            filesMarked.add(file1Name);
                            if (windowStart >= sysathand.GetEpsilon()) {
                                //add filename-string to a set-of-strings for the current batch
                                String file2Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "constraints_" + (windowStart - sysathand.GetEpsilon()) + "to" + (windowStart + sysathand.GetEpsilon()) + ".smt2";
                                filesMarked.add(file2Name);
                            }
                        }
                    }
                    /********************writing to all-snapshots file (counted or not)**************************/
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                    reportSnapshot(currentCPt,snapshot_outfile,  minCPtProc, markifcounted);
                    //}
                }//end of if overlap == number of processes
            }//end of if (minCPtProc!=-1)
        }while(minCPtProc!=-1);
        if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
            String smtOutputFile=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "SMTCuts.txt";
            int nwSmtCuts=processMarkedSMTfiles(filesMarked,smtOutputFile);//invoke this function even if filesMarked is empty because any unprocessed marked files from previous batch should be processed
            TraceHLCTimestampingOfflineArithPredDet.smtBasedSnapshotCount=TraceHLCTimestampingOfflineArithPredDet.smtBasedSnapshotCount+nwSmtCuts;
            //clear current changepoint queue and make the next batch's changepoint queue as the current batch's changepoint queue
            for(int i=0;i<sysathand.GetNumberOfProcesses();i++){//loop through all process queues
                Process currProc= mapofprocesses.get(i); //get the current state of the process
                currProc.deepCopyCurrentCPtQueue(currProc.getCPtQueueNextBatch());//make the next batch's queue as the current batch's queue
                currProc.clearNextChangePointQ();//clear next batch's changepoint queue
                mapofprocesses.put(i,currProc);
            }
        }
        System.out.println("Window based snapshot count so far:"+ TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount);
        System.out.println("SMT based snapshot count so far:"+ TraceHLCTimestampingOfflineArithPredDet.smtBasedSnapshotCount);
    }
    int getWindow(int cPtLvalue, int syseps) {
        int window=cPtLvalue/syseps;
        //System.out.println("smallestptincut:"+smallestptincut+";syseps:"+syseps+";Window:"+window);
        return window;
    }
    int findMinCptProc() {
        int minCPtProc=-1; //set to default value beginning
        Vector<Integer> temp= new Vector<Integer>();
        temp.add(0);
        temp.add(0);
        temp.add(0);
        //variable for finding and storing minimum changepoint
        ChangePoint minCPt= new ChangePoint(new HLC(temp),0,-1);
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process otherProc= mapofprocesses.get(i); //get the current state of the process
            Deque<ChangePoint> otherProccPtq=otherProc.getCPtQueue();//get the changepoint queue of the process
            if (!otherProccPtq.isEmpty())//if there is at least one unprocessed changepoint
            {
                ChangePoint cPt = otherProccPtq.getFirst();//get current first changepoint in queue
                if (minCPtProc==-1) //default value is -1,
                {
                    minCPt=cPt;	//setting the changepoint from the first process as minimum to start with
                    minCPtProc=i;
                }
                else{
                    int minl=minCPt.getcPointTimestamp().getClock().get(1);
                    int minc=minCPt.getcPointTimestamp().getClock().get(2);
                    int minPtType=minCPt.getEndPointType();
                    int currentl=cPt.getcPointTimestamp().getClock().get(1);
                    int currentc=cPt.getcPointTimestamp().getClock().get(2);
                    int currentPtType=cPt.getEndPointType();
                    //compare l and c values of all the smallest changepoints across processes
                    // if l and c values are equal then right endpoints have higher priority than left endpoints - i.e. they should be processed first
                    if (((currentl== minl)&&(currentc== minc)&&(currentPtType<minPtType)) || ((currentl< minl) || ((currentl== minl)&&(currentc< minc))))
                    {
                        minCPt=cPt;
                        minCPtProc=i;
                    }
                }
            }
        }
        return minCPtProc;
    }
    void printCandidatesForAllProc(String filename){
        File tmpDir = new File(filename);
        boolean exists = tmpDir.exists();
        if(!exists){
            fileClearCreateParentDirectory(filename);
        }
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCandQueueToFile(filename);
        }
    }
    void printChangepointsForAllProc(String filename){
        File tmpDir = new File(filename);
        boolean exists = tmpDir.exists();
        if(!exists){
            fileClearCreateParentDirectory(filename);
        }
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCPtQueueToFile(filename);
        }
    }
    void fileClearCreateParentDirectory(String filename){
        try{//clear current contents of the file
            File ifilename = new File(filename);
            ifilename.getParentFile().mkdirs();//create necessary parent directory
            new PrintWriter(filename).close();//clear current contents of the file
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
    int flexWindowCountSnapshot(ChangePoint currentCPt, int prevtokenend, int minCPtProc, String filename){
        /********Counting the snapshot only if it is epsilon away from previously detected snapshot********/
        int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        //if current overlap's i.e.changepoints' start-l is epsilon away from the previous overlap's start-l
        if((cPtLvalue-prevtokenend>sysathand.GetEpsilon()) || (TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount==0)){
            TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount++;
            //get/save the overlap's ending pt
            prevtokenend=cPtLvalue;
            /**********writing to snapshot_counted_outfile*******************/
            if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                writeSnapshotToFile(minCPtProc, currentCPt, filename,TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount);
            }
        }
        return prevtokenend;
    }
    boolean fixedWindowCountSnapshot(ChangePoint currentCPt,HashSet<Integer> windowsSeen, int minCPtProc, String filename){
        /***Counting the snapshot only if its current-epsilon-based window is different from the previously detected snapshot********/
        //int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        int cPtvalue = currentCPt.getcPointTimestamp().getClock().get(0);
        //compute the current cut's window based on epsilon
        int current_cut_window=getWindow(cPtvalue,sysathand.GetEpsilon());
        if((TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount==0)||(!windowsSeen.contains(current_cut_window)))
        {
            TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount++;
            windowsSeen.add(current_cut_window);
            //System.out.println("Counted.");
            //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1)
            {
                /***************writing to snapshot_window_counted_outfile************************/
                writeSnapshotToFile(minCPtProc,currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount);
            }
            return true;
        }
        return false;
    }
    void reportSnapshot(ChangePoint currentCPt, String filename, int minCPtProc, boolean markifcounted){
        TraceHLCTimestampingOfflineArithPredDet.snapshotcount++;
        writeSnapshotToFile(minCPtProc, currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.snapshotcount);
        if(markifcounted) {
            appendToFile(filename," Was Counted");
        }
    }
    void writeSnapshotToFile(int minCPtProc, ChangePoint currentCPt, String filename, int snapshotCount){
        try {
            BufferedWriter bw2 = new BufferedWriter(new FileWriter(filename, true));//true for append
            bw2.write("\n At Process"+minCPtProc+" Snapshot No:"+snapshotCount+"-->");
            bw2.write("[P"+minCPtProc+":<"+currentCPt.getcPointTimestamp().getClock().get(0)+",<"+currentCPt.getcPointTimestamp().getClock().get(1)+","+currentCPt.getcPointTimestamp().getClock().get(2)+">>");
            bw2.close();
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }
    void appendToFile(String filename, String text){
        try{
            File tmpDir = new File(filename);
            boolean exists = tmpDir.exists();
            if(!exists){
                fileClearCreateParentDirectory(filename);
            }
            BufferedWriter bw1=new BufferedWriter(new FileWriter(filename, true));//true for append
            bw1.write(text);
            bw1.close();
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
    /**This function creates a new constraint file for each marked/remembered-constraint file
     * adds common constraints like variable declaration, epsilon constraints, predicate/violation constraints to the new file,
     * adds interval and message constraints from the existing-marked constraint file,
     * adds upper and lower bound constraints for the timestamp-variable in the file,
     * and also adds a constraint to restrict detection of snapshot which is entirely present in the next batch.
     * Returns the number of snapshots detected i.e. number of smt files that resulted in SAT
     * Also deletes the files after processing them ***/
    int processMarkedSMTfiles(HashSet<String> smtFiles, String smtOutputFile){
        for(String unprocessedFile:fileToProcessDuringNxtBatch){//also process any unprocessed files
            smtFiles.add(unprocessedFile);
        }
        int smtSnapshotsCount=0;
        //for each marked file name
        for(String fileNm: smtFiles) {
            /***Determining if file belongs to current batch or (current batch and next batch)**/
            /***because we want to process only files that are complete and won't be appended to during the next batch***/
            //fetching window start pt from file name
            int windowSt=0, windowEnd=0;
            Pattern pattern4 = Pattern.compile("(constraints_)(\\d+)(to)(\\d+)(.smt2)");
            Matcher matcher4 = pattern4.matcher(fileNm);
            if (matcher4.find()) {
                windowSt=Integer.parseInt(matcher4.group(2));
                windowEnd=Integer.parseInt(matcher4.group(4));
            }
            //if file is in current batch
            if (windowEnd<=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength+sysathand.GetEpsilon()){
                if(fileToProcessDuringNxtBatch.contains(fileNm)) {
                    fileToProcessDuringNxtBatch.remove(fileNm);
                }
                System.out.println("Processing:"+fileNm);
                /***********Add variable declaration constraints, epsilon constraints, violation/predicate constraints*************/
                //new file for the updated constraints
                String newFileNm = fileNm.replace("constraints_","updatedConstraints_");
                appendToFile(newFileNm,commonConstraintsStr);//append constraints to new constraints-file
                /****************Add lower and upper bound constraints*********************/
                //add line by line from current file keep track of the lowest and highest timestamp for each process
                BufferedReader reader;
                BufferedWriter writer;
                /***adding interval and message constraints while simultaneously identifying lower and upper bounds for the timestamp variable based on timestamps in the file***/
                //vectors to keep track of lowest and highest timestamps for each process within each window/smt file
                Vector<Integer> lowestTimestamps = new Vector<Integer>(), highestTimestamps = new Vector<Integer>();
                for(int processId=0; processId<sysathand.GetNumberOfProcesses(); processId++){
                    lowestTimestamps.add(-1);//-1 will be used to check if the lowest timestamp was already identified in the file
                    highestTimestamps.add(0);
                }
                try {
                    reader = new BufferedReader(new FileReader(fileNm));
                    writer = new BufferedWriter(new FileWriter(newFileNm, true));//true for append
                    int leastTimeComputedForProcs=0;//variable to keep track of number of processes for which the lowest timestamps in the file were identified
                    String line = reader.readLine();
                    while (line != null) {//for each line in the existing constraint file
                        writer.write(line+"\n");
                        //identifying lowest timestamps for each process to specify lower bounds constraints
                        if(leastTimeComputedForProcs<sysathand.GetNumberOfProcesses()) {
                            Pattern pattern1 = Pattern.compile("(.*)(<=\\s)(\\d+)(\\sl)(\\d+)(.*)");//get first instance of this pattern in the file for each process
                            Matcher matcher1 = pattern1.matcher(line);
                            Pattern pattern3 = Pattern.compile("(.*)(not)(.*)");//to avoid getting lower bound from existing message constraint
                            Matcher matcher3 = pattern3.matcher(line);
                            if (matcher1.find() && !matcher3.find()) {
                                if (lowestTimestamps.elementAt(Integer.parseInt(matcher1.group(5))) == -1) {//if the lowest timestamp was not already identified for the process
                                    lowestTimestamps.setElementAt(Integer.parseInt(matcher1.group(3)), Integer.parseInt(matcher1.group(5)));//index is the second parameter
                                    leastTimeComputedForProcs++;
                                }}}
                        //identifying highest timestamps for each process to specify upper bounds constraints
                        Pattern pattern2 = Pattern.compile("(.*)(<\\sl)(\\d+)(\\s)(\\d+)(.*)");//get last instance of this pattern in the file for each process
                        Matcher matcher2 = pattern2.matcher(line);
                        if (matcher2.find()) {
                            highestTimestamps.setElementAt(Integer.parseInt(matcher2.group(5)), Integer.parseInt(matcher2.group(3)));//index is the second parameter
                        }
                        // read next line
                        line = reader.readLine();
                    }
                    writer.close();
                    reader.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                //adding lower and upper bound constraints
                //adding constraint to restrict at least one process' timestamp to be strictly within the current window - [window_start_pt to window_start_pt+epsilon instead of window_start_pt+2*epsilon]
                String boundConstraintsStr="",currentWindowConstraintStr="(assert ";
                //for each process
                for(int pr2=0; pr2 < sysathand.GetNumberOfProcesses(); pr2++){
                    //max(lowest, window start) becomes the lower bound - this forces the timestamp to be picked from the current window
                    boundConstraintsStr = boundConstraintsStr+"(assert (>= l"+pr2+" "+Math.max(lowestTimestamps.elementAt(pr2),windowSt)+"))\n";
                    //highest seen timestamp becomes the upper bound - make sure that it larger than the lower bound picked - UPPER BOUND constraints should be < and not <=
                    boundConstraintsStr = boundConstraintsStr+"(assert (< l"+pr2+" "+highestTimestamps.elementAt(pr2)+"))\n";
                    //constraint to force that at least one chosen timestamp in the snapshot falls in the current window - this is to avoid snapshots where all points in the snapshot are actually in the next window
                    if(pr2!=sysathand.GetNumberOfProcesses()-1){
                        currentWindowConstraintStr = currentWindowConstraintStr+"(or (< l"+pr2+" "+(windowSt+sysathand.GetEpsilon())+") ";
                    } else {
                        currentWindowConstraintStr=currentWindowConstraintStr+"(< l"+pr2+" "+(windowSt+sysathand.GetEpsilon())+")";
                    }
                }
                //adding necessary closing brackets
                for(int pr3=0; pr3 < sysathand.GetNumberOfProcesses(); pr3++) {
                    currentWindowConstraintStr=currentWindowConstraintStr+")";
                }
                currentWindowConstraintStr=currentWindowConstraintStr+"\n";
                appendToFile(newFileNm,boundConstraintsStr+currentWindowConstraintStr);
                //invoke solver on the new-constraints-file
                //if solver returned SAT then increment the snapshot counter
                if(smt2FileTest(newFileNm,smtOutputFile)){smtSnapshotsCount++;}
                //Delete processed constraint file and the corresponding original constraint file
                deleteFileIfExists(fileNm);
                deleteFileIfExists(newFileNm);
            } else{
                fileToProcessDuringNxtBatch.add(fileNm);
            }
        }//end of for loop to process all marked files
        return smtSnapshotsCount;
    }
    //Function smt2FileTest is from the below GITHUB repository
    /***************************************************************************************
     *    Title: Z3Prover
     *    Availability: https://github.com/Z3Prover/z3/blob/b7a27ca4bd25792208a77dae7e6023fce2a01291/examples/java/JavaExample.java
     ***************************************************************************************/
    boolean smt2FileTest(String filename, String smtOutputFile) {
        boolean sat=false;
        String smtOutputStr="";
        smtOutputStr="Processing "+filename+"\n";
        Date before = new Date();
        System.gc();
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        BoolExpr a = ctx.mkAnd(ctx.parseSMTLIB2File(filename, null, null, null, null));
        long t_diff = ((new Date()).getTime() - before.getTime());
        smtOutputStr=smtOutputStr+"SMT2 file read time: " + t_diff + " millisec\n";
        Solver solver1 = ctx.mkSimpleSolver();
        solver1.add(a);
        solver1.check();
        Status result1 = solver1.check();
        smtOutputStr=smtOutputStr+"Model check result  " + result1+"\n";
        System.out.println("Model check result  " + result1);
        t_diff = ((new Date()).getTime() - before.getTime());
        smtOutputStr=smtOutputStr+"SMT2 file check took " + t_diff + " millisec\n";
        if(result1.equals(Status.SATISFIABLE)) {
            final Model model = solver1.getModel();
            //System.out.println(model);
            for (FuncDecl constExpr : model.getConstDecls()) {//get interpretation of all consts in the model
                smtOutputStr=smtOutputStr+constExpr.getName()+":"+model.getConstInterp(constExpr)+"\n";
            }
            sat=true;
        }
        //record the SAT mode obtained
        appendToFile(smtOutputFile,smtOutputStr+"\n");
        return sat;
    }
    void deleteFileIfExists(String fullFileName){
        try {
            Files.deleteIfExists(Paths.get(fullFileName));
        }
        catch(NoSuchFileException e) {
            System.out.println("No such file/directory exists");
        }
        catch(DirectoryNotEmptyException e) {
            System.out.println("Directory is not empty.");
        }
        catch(IOException e) {
            System.out.println("Invalid permissions.");
        }
    }
}